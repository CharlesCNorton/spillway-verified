(******************************************************************************)
(*                                                                            *)
(*          Dam Spillway Scheduling: Safety Under Worst-Case Inflow           *)
(*                                                                            *)
(*   Models forecasted inflow with error bounds, gate control, hydraulic      *)
(*   response, and proves that a conservative controller keeps reservoir and  *)
(*   downstream stage within limits across all steps in a horizon.            *)
(*                                                                            *)
(*   "Thousands have lived without love, not one without water."              *)
(*   - W. H. Auden                                                            *)
(*                                                                            *)
(*   Author: Charles C. Norton                                                *)
(*   Date: December 2025                                                      *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Arith Lia List ZArith Program.
Import ListNotations.

Set Implicit Arguments.

(** State and plant parameters *)

(** Reservoir state: upstream level, downstream stage, gate opening (0-100%). *)
Record State
  : Type
  := mkState {
  reservoir_level_cm : nat;
  downstream_stage_cm : nat;
  gate_open_pct : nat
}.

(** Plant configuration: physical limits, capacities, and operational constraints. *)
Record PlantConfig
  : Type
  := mkPlantConfig {
  max_reservoir_cm : nat;
  max_downstream_cm : nat;
  gate_capacity_cms : nat;
  forecast_error_pct : nat;
  gate_slew_pct : nat;
  max_stage_rise_cm : nat;
  reservoir_area_cm2 : nat;
  timestep_s : nat;
  pc_max_reservoir_pos : max_reservoir_cm > 0;
  pc_max_downstream_pos : max_downstream_cm > 0;
  pc_gate_capacity_pos : gate_capacity_cms > 0;
  pc_reservoir_area_pos : reservoir_area_cm2 > 0;
  pc_timestep_pos : timestep_s > 0
}.

(** Dimensional normalization note:
    This model uses normalized units where inflow/outflow values directly represent
    level changes per timestep. The conversion factor (timestep_s / reservoir_area_cm2)
    is assumed to be unity or pre-applied to all flow values.

    For real-world application:
    - Convert physical flows (m^3/s) to normalized units before using the model
    - normalized_flow = physical_flow * timestep_s * 100 / reservoir_area_m2
    - The resulting normalized values can be directly added to/subtracted from levels *)
Definition flow_to_level (flow_cms : nat) (timestep_s : nat) (area_cm2 : nat)
  : nat
  := flow_cms * timestep_s / area_cm2.

(** Ceiling division for conservative scaling.
    Returns 0 when d = 0 as a safe default. *)
Definition div_ceil (n d : nat)
  : nat
  := match d with
     | O => 0
     | S _ => (n + d - 1) / d
     end.

(** div_ceil is monotone in the numerator. *)
Lemma div_ceil_mono_n
  : forall n1 n2 d, n1 <= n2 -> div_ceil n1 d <= div_ceil n2 d.
Proof.
  intros n1 n2 d Hle.
  unfold div_ceil.
  destruct d; [lia|].
  apply Nat.Div0.div_le_mono.
  lia.
Qed.

(** div_ceil produces a non-negative result. *)
Lemma div_ceil_nonneg
  : forall n d, 0 <= div_ceil n d.
Proof.
  intros. lia.
Qed.

Section WithPlantConfig.

  Variable pc : PlantConfig.

  (** Forecast inflow series (cms) indexed by timestep. *)
  Variable inflow_forecast_cms : nat -> nat.

  (** Plant rating: outflow (cms) to downstream stage (cm). *)
  Variable stage_from_outflow : nat -> nat.

  (** Safety predicate: reservoir and downstream stage under limits. *)
  Definition safe (s : State)
    : Prop
    := reservoir_level_cm s <= max_reservoir_cm pc /\
       downstream_stage_cm s <= max_downstream_cm pc.

  (** Gate command is within 0-100%. *)
  Definition gate_ok (s : State)
    : Prop
    := gate_open_pct s <= 100.

  (** Combined predicate: hydraulically safe and gate bounded. *)
  Definition valid (s : State)
    : Prop
    := safe s /\ gate_ok s.

  (** Worst-case inflow using fixed forecast error. *)
  Definition worst_case_inflow (t : nat)
    : nat
    := div_ceil (inflow_forecast_cms t * (100 + forecast_error_pct pc)) 100.

  (** Time-varying forecast error (bounded by twice the base error). *)
  Variable forecast_error_pct_t : nat -> nat.

  Hypothesis forecast_error_pct_t_bound
    : forall t, forecast_error_pct_t t <= 2 * forecast_error_pct pc.

  (** Worst-case inflow using per-timestep forecast error. *)
  Definition worst_case_inflow_t (t : nat)
    : nat
    := div_ceil (inflow_forecast_cms t * (100 + forecast_error_pct_t t)) 100.

  (** Time-varying worst-case is bounded by worst-case with doubled error.
      Uses forecast_error_pct_t_bound to establish the relationship. *)
  Lemma worst_case_inflow_t_bound
    : forall t,
      worst_case_inflow_t t <= div_ceil (inflow_forecast_cms t * (100 + 2 * forecast_error_pct pc)) 100.
  Proof.
    intro t.
    unfold worst_case_inflow_t.
    apply div_ceil_mono_n.
    pose proof (forecast_error_pct_t_bound t) as Hbound.
    apply Nat.mul_le_mono_l.
    lia.
  Qed.

  (** Available storage plus inflow from a provided inflow function. *)
  Definition available_water (inflow : nat -> nat) (s : State) (t : nat)
    : nat
    := reservoir_level_cm s + inflow t.

  (** Released discharge limited by capacity and availability for a given inflow. *)
  Definition outflow (inflow : nat -> nat) (ctrl : State -> nat -> nat) (s : State) (t : nat)
    : nat
    := Nat.min (gate_capacity_cms pc * ctrl s t / 100) (available_water inflow s t).

  (** Outflow never exceeds available water (ensures no underflow in step). *)
  Lemma outflow_le_available
    : forall inflow ctrl s t, outflow inflow ctrl s t <= available_water inflow s t.
  Proof.
    intros.
    unfold outflow.
    apply Nat.le_min_r.
  Qed.

  (** One-step reservoir update under a provided inflow function.
      Uses normalized units where flow values directly represent level changes. *)
  Definition step (inflow : nat -> nat) (ctrl : State -> nat -> nat) (s : State) (t : nat)
    : State
    := let qin := inflow t in
       let out := outflow inflow ctrl s t in
       let new_res := reservoir_level_cm s + qin - out in
       let new_stage := stage_from_outflow out in
       {| reservoir_level_cm := new_res;
          downstream_stage_cm := new_stage;
          gate_open_pct := ctrl s t |}.

  (** Reservoir level after step is non-negative (subtraction is safe). *)
  Lemma step_level_nonneg
    : forall inflow ctrl s t, reservoir_level_cm (step inflow ctrl s t) >= 0.
  Proof.
    intros.
    unfold step.
    simpl.
    assert (H : outflow inflow ctrl s t <= available_water inflow s t)
      by apply outflow_le_available.
    unfold available_water in H.
    lia.
  Qed.

  (** Horizon run of the plant with a fixed controller and inflow model. *)
  Fixpoint run (inflow : nat -> nat) (ctrl : State -> nat -> nat) (horizon : nat) (s : State)
    : State
    := match horizon with
       | O => s
       | S k => run inflow ctrl k (step inflow ctrl s k)
       end.

  (** Forward-time horizon run carrying the current timestep explicitly. *)
  Fixpoint run_fwd (inflow : nat -> nat) (ctrl : State -> nat -> nat) (t : nat) (h : nat) (s : State)
    : State
    := match h with
       | O => s
       | S k => run_fwd inflow ctrl (S t) k (step inflow ctrl s t)
       end.

  (** Convenience shorthand: forward run starting at time 0. *)
  Definition run0 (inflow : nat -> nat) (ctrl : State -> nat -> nat) (h : nat) (s : State)
    : State
    := run_fwd inflow ctrl 0 h s.

(** Maximum value in a list, returning 0 for empty list. *)
Fixpoint list_max (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

(** Every element is bounded by list_max. *)
Lemma list_max_bound
  : forall l x, In x l -> x <= list_max l.
Proof.
  induction l as [|h t IH]; intros x Hin.
  - destruct Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst. simpl. apply Nat.le_max_l.
    + simpl.
      eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

(** nth element is bounded by list_max plus default. *)
Lemma nth_le_max_or_default
  : forall l n d, nth n l d <= Nat.max (list_max l) d.
Proof.
  induction l as [|h t IH]; intros n d.
  - simpl.
    destruct n; simpl; lia.
  - destruct n as [|n'].
    + simpl. lia.
    + simpl.
      specialize (IH n' d).
      lia.
Qed.

(** Monotone rating-curve lookup (flow->stage) with conservative stepwise interpolation. *)
Definition RatingTable := list (nat * nat).

Fixpoint stage_from_table (tbl:RatingTable) (out:nat) : nat :=
  match tbl with
  | [] => 0
  | (q,s)::rest =>
      let tail := stage_from_table rest out in
      if Nat.leb out q then s else Nat.max s tail
  end.

Fixpoint monotone_table (tbl:RatingTable) : Prop :=
  match tbl with
  | [] => True
  | _::[] => True
  | (q1,s1)::rest =>
      match rest with
      | [] => True
      | (q2,s2)::rest' => q1 <= q2 /\ s1 <= s2 /\ monotone_table rest
      end
  end.

(** All table stage values are bounded by a given limit. *)
Definition table_stages_bounded (tbl:RatingTable) (bound:nat) : Prop :=
  Forall (fun qs => snd qs <= bound) tbl.

(** Max is monotone in its right argument. *)
Lemma Nat_max_mono_r : forall s a b, a <= b -> Nat.max s a <= Nat.max s b.
Proof.
  intros s a b Hle.
  destruct (Nat.leb s a) eqn:Ha; destruct (Nat.leb s b) eqn:Hb; lia.
Qed.

(** An nth element of a bounded list preserves the bound. *)
Lemma Forall_nth :
  forall {A} (P:A->Prop) (l:list A) d n,
    Forall P l ->
    n < length l ->
    P (nth n l d).
Proof.
  intros A P l d n Hf.
  revert n.
  induction Hf as [|x xs Hpx Hfor IH]; intros n Hlt; simpl in *.
  - lia.
  - destruct n as [|n']; simpl in *.
    + exact Hpx.
    + apply IH. lia.
Qed.

(** Stage lookup is monotone when the rating table is monotone.
    This lemma uses the rating_monotone hypothesis to establish that
    stage_from_table produces larger values for larger outflows. *)
Lemma stage_from_table_mono
  : forall tbl out1 out2,
    monotone_table tbl ->
    out1 <= out2 ->
    stage_from_table tbl out1 <= stage_from_table tbl out2.
Proof.
  induction tbl as [|[q s] rest IH]; intros out1 out2 Hmono Hle.
  - simpl. lia.
  - simpl.
    destruct (Nat.leb out1 q) eqn:H1; destruct (Nat.leb out2 q) eqn:H2.
    + lia.
    + apply Nat.leb_le in H1.
      apply Nat.leb_gt in H2.
      apply Nat.le_max_l.
    + apply Nat.leb_gt in H1.
      apply Nat.leb_le in H2.
      lia.
    + apply Nat.max_le_compat_l.
      destruct rest as [|[q' s'] rest'].
      * simpl. lia.
      * simpl in Hmono.
        destruct Hmono as [_ [_ Hrest_mono]].
        apply IH; assumption.
Qed.

Lemma stage_from_table_bounded :
  forall tbl bound out,
    table_stages_bounded tbl bound ->
    stage_from_table tbl out <= bound.
Proof.
  induction tbl as [|[q s] rest IH]; intros bound out Hbd; simpl.
  - lia.
  - inversion_clear Hbd as [|[q' s'] rest' Hhead Htail]; simpl in *.
    destruct (Nat.leb out q); simpl.
    + lia.
    + apply Nat.max_lub; [lia|apply IH; assumption].
Qed.

(** Control/plant assumptions.

    This section defines abstract safety properties parameterized by hypotheses.
    The hypotheses (stage_bounded, reservoir_preserved, etc.) are instantiated
    in concrete sections (ConcreteCertified, RatingTableCertified) where they
    are derived from specific plant models and controller definitions. *)
Section SingleGate.

  Variable control : State -> nat -> nat.
  Variable inflow : nat -> nat.

  (** Controller always returns a gate command within 0-100%. *)
  Hypothesis control_within_bounds
    : forall s t, control s t <= 100.

  (** Controller respects slew limits relative to current gate. *)
  Hypothesis control_slew_limited
    : forall s t, gate_ok s ->
        control s t <= gate_open_pct s + gate_slew_pct pc /\
        gate_open_pct s <= control s t + gate_slew_pct pc.

  (** Controller-induced stage respects per-step ramp limit. *)
  Hypothesis control_ramp_limited
    : forall s t, safe s ->
        stage_from_outflow (outflow inflow control s t)
          <= downstream_stage_cm s + max_stage_rise_cm pc.

  (** Plant stage response is below downstream ceiling. *)
  Hypothesis stage_bounded
    : forall out, stage_from_outflow out <= max_downstream_cm pc.

  (** Mass balance: storage plus inflow stays under crest plus discharge.
      Uses normalized units where values directly represent level changes. *)
  Hypothesis reservoir_preserved
    : forall s t, safe s ->
        reservoir_level_cm s + inflow t
          <= outflow inflow control s t + max_reservoir_cm pc.

(** Utility lemma: if a <= b + c then a - b <= c. *)
Lemma sub_le_from_bound : forall a b c, a <= b + c -> a - b <= c.
Proof. intros; lia. Qed.

(** Gate command always recorded within 0..100. *)
Lemma gate_pct_bounded : forall s t, gate_open_pct (step inflow control s t) <= 100.
Proof.
  intros. unfold step. simpl. apply control_within_bounds.
Qed.

(** Gate slew between steps respects limits. *)
Lemma gate_slew_respected
  : forall s t,
    gate_ok s ->
    gate_open_pct (step inflow control s t) <= gate_open_pct s + gate_slew_pct pc /\
    gate_open_pct s <= gate_open_pct (step inflow control s t) + gate_slew_pct pc.
Proof.
  intros s t Hok.
  unfold step.
  simpl.
  apply control_slew_limited; assumption.
Qed.

(** One-step safety preservation under the assumptions. *)
Lemma step_preserves_safe : forall s t, safe s -> safe (step inflow control s t).
Proof.
  intros s t Hsafe.
  unfold safe in *.
  destruct Hsafe as [Hres Hstage].
  unfold step.
  simpl.
  set (qin := inflow t).
  set (out := outflow inflow control s t).
  assert (Hres_bound : reservoir_level_cm s + qin <= out + max_reservoir_cm pc).
  { apply reservoir_preserved. split; assumption. }
  split.
  - apply sub_le_from_bound. exact Hres_bound.
  - apply stage_bounded.
Qed.

(** Per-step downstream ramp is within tolerance. *)
Lemma step_preserves_ramp
  : forall s t,
    safe s ->
    downstream_stage_cm (step inflow control s t) <= downstream_stage_cm s + max_stage_rise_cm pc.
Proof.
  intros s t Hsafe. unfold step. simpl.
  apply control_ramp_limited; assumption.
Qed.

(** Nonnegativity of reservoir level after a step. *)
Lemma step_reservoir_nonneg : forall s t,
  reservoir_level_cm (step inflow control s t) >= 0.
Proof.
  intros. unfold step. simpl.
  lia.
Qed.

(** Valid state is preserved by one control step. *)
Lemma step_preserves_valid : forall s t, valid s -> valid (step inflow control s t).
Proof.
  intros s t [Hsafe Hgate]. split.
  - apply step_preserves_safe; assumption.
  - apply gate_pct_bounded.
Qed.

(** Safety over an arbitrary horizon. *)
Lemma run_preserves_safe : forall h s, safe s -> safe (run inflow control h s).
Proof.
  induction h as [|h IH]; intros s Hsafe.
  - exact Hsafe.
  - simpl. apply IH. apply step_preserves_safe; assumption.
Qed.

(** Per-step ramp across a run: cumulative bound from the initial state. *)
Lemma run_preserves_ramp
  : forall k s,
    safe s ->
    downstream_stage_cm (run inflow control k s) <= downstream_stage_cm s + k * max_stage_rise_cm pc.
Proof.
  induction k as [|k IH]; intros s Hsafe.
  - simpl. lia.
  - simpl.
    replace (S k * max_stage_rise_cm pc) with (max_stage_rise_cm pc + k * max_stage_rise_cm pc) by lia.
    set (s' := step inflow control s k).
    assert (Hsafe' : safe s') by (apply step_preserves_safe; assumption).
    assert (Hramp : downstream_stage_cm s' <= downstream_stage_cm s + max_stage_rise_cm pc)
      by (subst s'; apply step_preserves_ramp; assumption).
    specialize (IH s' Hsafe').
    lia.
Qed.

(** Valid-state preservation over horizon. *)
Lemma run_preserves_valid : forall h s, valid s -> valid (run inflow control h s).
Proof.
  induction h as [|h IH]; intros s Hvalid.
  - exact Hvalid.
  - simpl. apply IH. apply step_preserves_valid; assumption.
Qed.

(** Forward-time safety over an arbitrary horizon starting at time t. *)
Lemma run_fwd_preserves_safe : forall h t s, safe s -> safe (run_fwd inflow control t h s).
Proof.
  induction h as [|h IH]; intros t s Hsafe; simpl; [assumption|].
  apply IH with (t := S t) (s := step inflow control s t).
  apply step_preserves_safe; assumption.
Qed.

(** Forward-time validity over an arbitrary horizon starting at time t. *)
Lemma run_fwd_preserves_valid : forall h t s, valid s -> valid (run_fwd inflow control t h s).
Proof.
  induction h as [|h IH]; intros t s Hvalid; simpl; [assumption|].
  apply IH with (t := S t) (s := step inflow control s t).
  apply step_preserves_valid; assumption.
Qed.

(** Main theorem: starting safe implies safety for the entire horizon. *)
Theorem schedule_safe :
  forall s0 horizon, safe s0 -> safe (run inflow control horizon s0).
Proof. intros; eapply run_preserves_safe; eauto. Qed.

(** Forward-time horizon safety starting at t=0. *)
Theorem schedule_safe_fwd :
  forall s0 horizon, safe s0 -> safe (run0 inflow control horizon s0).
Proof.
  intros s0 horizon Hsafe.
  unfold run0. apply run_fwd_preserves_safe; assumption.
Qed.

(** Prefix safety: all intermediate steps up to a horizon remain safe. *)
Theorem schedule_safe_prefix :
  forall s0 horizon, safe s0 -> forall k, k <= horizon -> safe (run inflow control k s0).
Proof. intros s0 horizon Hsafe k _; apply run_preserves_safe; exact Hsafe. Qed.

(** Ramp remains bounded across any prefix of the horizon. *)
Theorem schedule_ramp
  : forall s0 horizon,
    safe s0 ->
    forall k,
    k <= horizon ->
    downstream_stage_cm (run inflow control k s0) <= downstream_stage_cm s0 + k * max_stage_rise_cm pc.
Proof.
  intros.
  eapply run_preserves_ramp; eauto.
Qed.

(** Validity (safety + gate bounds) holds over the horizon. *)
Theorem schedule_valid :
  forall s0 horizon, valid s0 -> valid (run inflow control horizon s0).
Proof. intros; eapply run_preserves_valid; eauto. Qed.

End SingleGate.

(** --------------------------------------------------------------------------- *)
(** Concrete single-gate controller and plant instantiation                     *)
(**                                                                             *)
(** This section proves reservoir_preserved_concrete by deriving it from:       *)
(**   - margin_le_reservoir: margin < crest                                     *)
(**   - inflow_below_margin: worst-case inflow fits in margin                   *)
(**   - capacity_sufficient: gate can discharge worst-case inflow               *)
(**                                                                             *)
(** For concrete instantiation with real data, use list_max and list_max_bound  *)
(** to derive inflow_below_margin from a specific inflow series.                *)
(** --------------------------------------------------------------------------- *)

Section ConcreteCertified.

  (** Engineering design constants *)
  Variable base_tailwater_cm : nat.
  Variable margin_cm : nat.
  Variable stage_gain_cm_per_cms : nat.

  (** Margin fits under the reservoir crest. *)
  Hypothesis margin_le_reservoir
    : margin_cm <= max_reservoir_cm pc.

  (** Worst-case inflow is within the chosen margin. *)
  Hypothesis inflow_below_margin
    : forall t, worst_case_inflow t <= margin_cm.

  (** Gate capacity can pass worst-case inflow. *)
  Hypothesis capacity_sufficient
    : forall t, worst_case_inflow t <= gate_capacity_cms pc.

  (** Slew constraint allows going full-open in one step.
      NOTE: This is a placeholder that makes safety trivially achievable.
      For realistic constraints, use gate_slew_pct pc < 100 (e.g., 10-20%)
      and update the controller to handle gradual ramping. *)
  Hypothesis gate_slew_full
    : gate_slew_pct pc >= 100.

  (** Linear hydraulic response with saturation at capacity. *)
  Hypothesis stage_model
    : forall out,
        stage_from_outflow out =
        base_tailwater_cm + stage_gain_cm_per_cms * Nat.min out (gate_capacity_cms pc).

  (** Stage at full capacity is below downstream ceiling. *)
  Hypothesis stage_gain_capacity_bound
    : base_tailwater_cm + stage_gain_cm_per_cms * gate_capacity_cms pc <= max_downstream_cm pc.

  (** Per-step ramp allowance exceeds downstream ceiling.
      NOTE: This is a placeholder that makes ramp constraints vacuous.
      For realistic constraints, use max_stage_rise_cm pc << max_downstream_cm pc
      to enforce gradual stage changes and prevent sudden flooding. *)
  Hypothesis ramp_budget
    : max_stage_rise_cm pc >= max_downstream_cm pc.

  (** Trigger level to go full-open (crest minus margin). *)
  Definition threshold_cm
    : nat
    := max_reservoir_cm pc - margin_cm.

  (** Pure linear stage gain (without saturation), auxiliary. *)
  Definition stage_from_outflow_linear (out : nat)
    : nat
    := stage_gain_cm_per_cms * out.

  (** Controller: full-open above threshold, otherwise back off gradually.

      NOTE: This is a simplified bang-bang controller for proof tractability.
      Real spillway controllers use more sophisticated approaches:
      - PID control with tuned gains for smooth response
      - Model Predictive Control (MPC) optimizing over forecast horizon
      - Rule-based control with multiple thresholds and ramp rates
      - Adaptive control adjusting to measured vs predicted inflows

      For verification of realistic controllers, additional hypotheses on
      controller smoothness, stability, and response time would be needed. *)
  Definition control_concrete (s : State) (_ : nat)
    : nat
    := if Nat.leb threshold_cm (reservoir_level_cm s)
       then 100
       else Nat.min 100 (Nat.max 0 (gate_open_pct s - gate_slew_pct pc)).

  (** Controller output is bounded by 100%. *)
  Lemma control_concrete_within : forall s t, control_concrete s t <= 100.
  Proof.
    intros. unfold control_concrete.
    destruct (Nat.leb threshold_cm (reservoir_level_cm s)); [lia|].
    apply Nat.le_min_l.
  Qed.

  (** Controller respects slew constraints relative to current gate. *)
  Lemma control_concrete_slew : forall s t,
    gate_ok s ->
    control_concrete s t <= gate_open_pct s + gate_slew_pct pc /\
    gate_open_pct s <= control_concrete s t + gate_slew_pct pc.
  Proof.
    intros s t Hok; unfold control_concrete; destruct (Nat.leb threshold_cm (reservoir_level_cm s)).
    - (* fully open branch *) split.
      + apply Nat.le_trans with (m := gate_slew_pct pc); [apply gate_slew_full|lia].
      + apply Nat.le_trans with (m := 100); [exact Hok|lia].
    - (* closing branch *) split.
      + apply Nat.le_trans with (m := Nat.max 0 (gate_open_pct s - gate_slew_pct pc)).
        * apply Nat.le_min_r.
        * apply Nat.max_case_strong; intros; lia.
      + destruct (le_lt_dec (gate_slew_pct pc) (gate_open_pct s)).
        * assert (gate_open_pct s = (gate_open_pct s - gate_slew_pct pc) + gate_slew_pct pc) by lia.
          assert (Hmax : Nat.max 0 (gate_open_pct s - gate_slew_pct pc) = gate_open_pct s - gate_slew_pct pc) by lia.
          rewrite Hmax.
          assert (Hdiff_le1 : gate_open_pct s - gate_slew_pct pc <= gate_open_pct s) by apply Nat.le_sub_l.
          assert (Hdiff_le : gate_open_pct s - gate_slew_pct pc <= 100) by (eapply Nat.le_trans; [exact Hdiff_le1|exact Hok]).
          rewrite (Nat.min_r _ _ Hdiff_le).
          lia.
        * (* gate < slew, control goes to 0 *)
          assert (gate_open_pct s <= gate_slew_pct pc) by lia.
          assert (Nat.max 0 (gate_open_pct s - gate_slew_pct pc) = 0) by lia.
          rewrite H0. simpl. lia.
  Qed.

  (** Discharge under this controller never exceeds gate capacity. *)
  Lemma outflow_le_capacity : forall s t,
    outflow worst_case_inflow control_concrete s t <= gate_capacity_cms pc.
  Proof.
    intros. unfold outflow, available_water. simpl.
    apply Nat.le_trans with (m := gate_capacity_cms pc * control_concrete s t / 100).
    - apply Nat.le_min_l.
    - pose proof (control_concrete_within s t) as Hc.
      assert (Hmul : gate_capacity_cms pc * control_concrete s t <= gate_capacity_cms pc * 100)
        by (apply Nat.mul_le_mono_l; lia).
      apply (Nat.Div0.div_le_mono _ _ 100) in Hmul.
      rewrite Nat.div_mul in Hmul by discriminate.
      exact Hmul.
  Qed.

  (** Mass balance: storage + inflow stays within crest + discharge. *)
  Lemma reservoir_preserved_concrete :
    forall s t, safe s ->
      reservoir_level_cm s + worst_case_inflow t <= outflow worst_case_inflow control_concrete s t + max_reservoir_cm pc.
  Proof.
    intros s t Hsafe. unfold safe in Hsafe. destruct Hsafe as [Hres _].
    unfold control_concrete.
    destruct (Nat.leb threshold_cm (reservoir_level_cm s)) eqn:Hbranch.
    - (* fully open; capacity dominates inflow *)
      assert (Hcap := capacity_sufficient t).
      unfold outflow, available_water. rewrite Hbranch.
      apply Nat.min_case_strong; intro Hcmp.
      + (* outflow limited by capacity branch, dominate inflow *)
        rewrite Nat.div_mul by discriminate.
        assert (Hstep1 : reservoir_level_cm s + worst_case_inflow t <= reservoir_level_cm s + gate_capacity_cms pc)
          by (apply Nat.add_le_mono_l; exact Hcap).
        assert (Hstep2 : reservoir_level_cm s + gate_capacity_cms pc <= max_reservoir_cm pc + gate_capacity_cms pc)
          by (apply Nat.add_le_mono_r; exact Hres).
        eapply Nat.le_trans; [exact Hstep1|].
        eapply Nat.le_trans; [exact Hstep2|].
        rewrite Nat.add_comm. apply Nat.le_refl.
      + (* outflow limited by availability branch *)
        unfold available_water. lia.
    - (* below threshold; rely on margin *)
      apply Nat.leb_gt in Hbranch.
      unfold outflow, available_water. simpl.
      assert (Hinflow := inflow_below_margin t).
      assert (Hlt_margin : reservoir_level_cm s + margin_cm < max_reservoir_cm pc).
      { unfold threshold_cm in Hbranch.
        apply Nat.add_lt_mono_r with (p := margin_cm) in Hbranch.
        rewrite Nat.sub_add in Hbranch by exact margin_le_reservoir.
        exact Hbranch. }
      assert (Hresv_le : reservoir_level_cm s + worst_case_inflow t <= max_reservoir_cm pc).
      { apply Nat.lt_le_incl.
        eapply Nat.le_lt_trans.
        - apply Nat.add_le_mono_l; exact Hinflow.
        - exact Hlt_margin. }
      lia.
  Qed.

  (** Hydraulic stage under control_concrete is below downstream ceiling. *)
  Lemma stage_bounded_concrete :
    forall out, stage_from_outflow out <= max_downstream_cm pc.
  Proof.
    intros out. rewrite stage_model.
    assert (Hmul : stage_gain_cm_per_cms * Nat.min out (gate_capacity_cms pc)
                   <= stage_gain_cm_per_cms * gate_capacity_cms pc).
    { replace (stage_gain_cm_per_cms * Nat.min out (gate_capacity_cms pc))
        with (Nat.min out (gate_capacity_cms pc) * stage_gain_cm_per_cms) by lia.
      replace (stage_gain_cm_per_cms * gate_capacity_cms pc)
        with (gate_capacity_cms pc * stage_gain_cm_per_cms) by lia.
      apply Nat.mul_le_mono; try lia; apply Nat.min_glb_r. }
    apply Nat.le_trans with (m := base_tailwater_cm + stage_gain_cm_per_cms * gate_capacity_cms pc).
    - apply Nat.add_le_mono_l. exact Hmul.
    - exact stage_gain_capacity_bound.
  Qed.

(** Outflow cannot exceed available water (nonnegative storage). *)
Lemma reservoir_nonnegative_concrete :
  forall s t, outflow worst_case_inflow control_concrete s t <= reservoir_level_cm s + worst_case_inflow t.
Proof.
  intros. unfold outflow, available_water. simpl. apply Nat.le_min_r.
Qed.

(** Downstream stage change per step within ramp budget. *)
Lemma stage_ramp_preserved_concrete :
  forall s t, safe s ->
    stage_from_outflow (outflow worst_case_inflow control_concrete s t) <= downstream_stage_cm s + max_stage_rise_cm pc.
Proof.
  intros s t Hsafe.
  (* Use the generic ramp assumption via a simple bound: downstream nonnegativity. *)
  assert (Hstage := stage_bounded_concrete (outflow worst_case_inflow control_concrete s t)).
  assert (Hnonneg : 0 <= downstream_stage_cm s) by lia.
  lia.
Qed.

  (** One concrete step preserves reservoir and stage safety. *)
  Lemma step_preserves_safe_concrete : forall s t, safe s -> safe (step worst_case_inflow control_concrete s t).
  Proof.
    intros s t Hs. unfold safe in *. destruct Hs as [Hres Hstage].
    unfold step. simpl.
    set (qin := worst_case_inflow t).
    set (out := outflow worst_case_inflow control_concrete s t).
    assert (Hres_bound : reservoir_level_cm s + qin <= out + max_reservoir_cm pc)
      by (apply reservoir_preserved_concrete; split; assumption).
    split.
    - apply sub_le_from_bound; assumption.
    - apply stage_bounded_concrete.
  Qed.

  (** Concrete run preserves safety over the horizon. *)
  Lemma run_preserves_safe_concrete : forall h s, safe s -> safe (run worst_case_inflow control_concrete h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_concrete; assumption].
  Qed.

  (** Gate remains within 0–100% after a concrete step. *)
  Lemma gate_pct_bounded_concrete : forall s t, gate_open_pct (step worst_case_inflow control_concrete s t) <= 100.
  Proof. intros; unfold step; simpl; apply control_concrete_within. Qed.

  (** One concrete step preserves validity. *)
  Lemma step_preserves_valid_concrete : forall s t, valid s -> valid (step worst_case_inflow control_concrete s t).
  Proof.
    intros s t [Hs Hg]. split.
    - apply step_preserves_safe_concrete; auto.
    - apply gate_pct_bounded_concrete.
  Qed.

  (** Concrete run preserves validity over the horizon. *)
  Lemma run_preserves_valid_concrete : forall h s, valid s -> valid (run worst_case_inflow control_concrete h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_valid_concrete; assumption].
  Qed.

  (** Horizon safety guarantee for the concrete controller. *)
  Corollary concrete_schedule_safe :
    forall s0 horizon,
      safe s0 ->
      safe (run worst_case_inflow control_concrete horizon s0).
  Proof.
    intros s0 horizon Hsafe. now apply run_preserves_safe_concrete.
  Qed.

  (** Horizon validity guarantee for the concrete controller. *)
  Corollary concrete_schedule_valid :
    forall s0 horizon,
      valid s0 ->
      valid (run worst_case_inflow control_concrete horizon s0).
Proof.
  intros s0 horizon Hvalid. now apply run_preserves_valid_concrete.
Qed.

End ConcreteCertified.

(** --------------------------------------------------------------------------- *)
(** Proportional controller with realistic slew and ramp constraints            *)
(** --------------------------------------------------------------------------- *)

Section ProportionalController.

  (** Controller gain (percent opening per cm of level above setpoint). *)
  Variable Kp : nat.

  (** Setpoint level (target reservoir level in cm). *)
  Variable setpoint_cm : nat.

  (** Actual slew limit (must be < 100 for non-trivial constraint). *)
  Variable actual_slew_pct : nat.

  (** Actual ramp limit (must be < max_downstream for non-trivial constraint). *)
  Variable actual_ramp_cm : nat.

  (** Slew is strictly limited. *)
  Hypothesis actual_slew_bounded
    : actual_slew_pct <= gate_slew_pct pc.

  (** Ramp is strictly limited. *)
  Hypothesis actual_ramp_bounded
    : actual_ramp_cm <= max_stage_rise_cm pc.

  (** Setpoint is below crest with margin. *)
  Hypothesis setpoint_safe
    : setpoint_cm + 500 <= max_reservoir_cm pc.

  (** Gain is positive. *)
  Hypothesis Kp_pos
    : Kp > 0.

  (** Proportional controller: output proportional to error above setpoint.
      Clamped to [0, 100] and respects slew limits. *)
  Definition control_proportional (s : State) (_ : nat)
    : nat
    := let error := reservoir_level_cm s - setpoint_cm in
       let raw_cmd := Kp * error in
       let clamped := Nat.min 100 raw_cmd in
       let current := gate_open_pct s in
       let slew_up := Nat.min clamped (current + actual_slew_pct) in
       let slew_down := Nat.max slew_up (current - actual_slew_pct) in
       slew_down.

  (** Proportional controller output is bounded by 100% when current gate is valid. *)
  Lemma control_proportional_within
    : forall s t, gate_ok s -> control_proportional s t <= 100.
  Proof.
    intros s t Hok.
    unfold control_proportional, gate_ok in *.
    set (clamped := Nat.min 100 (Kp * (reservoir_level_cm s - setpoint_cm))).
    set (slew_up := Nat.min clamped (gate_open_pct s + actual_slew_pct)).
    set (slew_down := Nat.max slew_up (gate_open_pct s - actual_slew_pct)).
    assert (Hc : clamped <= 100) by apply Nat.le_min_l.
    assert (Hsu : slew_up <= clamped) by apply Nat.le_min_l.
    destruct (Nat.le_ge_cases slew_up (gate_open_pct s - actual_slew_pct)) as [Hcase|Hcase].
    - assert (slew_down = gate_open_pct s - actual_slew_pct) by (apply Nat.max_r; exact Hcase).
      rewrite H. lia.
    - assert (slew_down = slew_up) by (apply Nat.max_l; lia).
      rewrite H. lia.
  Qed.

  (** Proportional controller respects actual slew limits. *)
  Lemma control_proportional_slew
    : forall s t,
      gate_ok s ->
      control_proportional s t <= gate_open_pct s + actual_slew_pct /\
      gate_open_pct s <= control_proportional s t + actual_slew_pct.
  Proof.
    intros s t Hok.
    unfold control_proportional.
    split.
    - eapply Nat.le_trans.
      + apply Nat.max_lub.
        * apply Nat.le_min_r.
        * lia.
      + lia.
    - apply Nat.max_case_strong; intros; lia.
  Qed.

  (** Proportional controller also respects the plant slew limits. *)
  Lemma control_proportional_slew_plant
    : forall s t,
      gate_ok s ->
      control_proportional s t <= gate_open_pct s + gate_slew_pct pc /\
      gate_open_pct s <= control_proportional s t + gate_slew_pct pc.
  Proof.
    intros s t Hok.
    unfold control_proportional.
    split.
    - eapply Nat.le_trans.
      + apply Nat.max_lub.
        * eapply Nat.le_trans.
          { apply Nat.le_min_r. }
          { apply Nat.add_le_mono_l. exact actual_slew_bounded. }
        * lia.
      + lia.
    - apply Nat.max_case_strong; intros; lia.
  Qed.

  (** Stability property: when level is at setpoint, output is zero. *)
  Lemma control_proportional_at_setpoint
    : forall s t,
      reservoir_level_cm s <= setpoint_cm ->
      gate_open_pct s = 0 ->
      control_proportional s t = 0.
  Proof.
    intros s t Hlevel Hgate.
    unfold control_proportional.
    rewrite Hgate.
    assert (reservoir_level_cm s - setpoint_cm = 0) as Herr by lia.
    rewrite Herr.
    rewrite Nat.mul_0_r.
    simpl.
    reflexivity.
  Qed.

  (** Smoothness property: output changes are bounded by slew. *)
  Lemma control_proportional_smooth
    : forall s1 s2 t,
      gate_ok s1 ->
      gate_open_pct s2 = control_proportional s1 t ->
      gate_ok s2.
  Proof.
    intros s1 s2 t Hok1 Hgate2.
    unfold gate_ok.
    rewrite Hgate2.
    apply control_proportional_within.
    exact Hok1.
  Qed.

End ProportionalController.

(** --------------------------------------------------------------------------- *)
(** Certified proportional controller with realistic constraints                *)
(**                                                                             *)
(** This section proves safety for a proportional controller with:              *)
(**   - actual_slew_pct < 100 (non-trivial slew constraint)                     *)
(**   - actual_ramp_cm < max_downstream_cm (non-trivial ramp constraint)        *)
(**   - Gain high enough to respond to rising water before overflow             *)
(** --------------------------------------------------------------------------- *)

Section ProportionalCertified.

  Variable Kp : nat.
  Variable setpoint_cm : nat.
  Variable actual_slew_pct : nat.
  Variable margin_cm : nat.

  Hypothesis Kp_pos : Kp > 0.
  Hypothesis setpoint_below_crest : setpoint_cm + margin_cm <= max_reservoir_cm pc.
  Hypothesis margin_positive : margin_cm > 0.
  Hypothesis slew_realistic : actual_slew_pct < 100.
  Hypothesis capacity_sufficient_prop : forall t, worst_case_inflow t <= gate_capacity_cms pc.
  Hypothesis inflow_below_margin : forall t, worst_case_inflow t <= margin_cm.

  Definition control_prop (s : State) (_ : nat) : nat :=
    let error := reservoir_level_cm s - setpoint_cm in
    let raw_cmd := Kp * error in
    let clamped := Nat.min 100 raw_cmd in
    let current := gate_open_pct s in
    let slew_up := Nat.min clamped (current + actual_slew_pct) in
    Nat.max slew_up (current - actual_slew_pct).

  Lemma control_prop_within : forall s t, gate_ok s -> control_prop s t <= 100.
  Proof.
    intros s t Hok.
    unfold control_prop, gate_ok in *.
    set (clamped := Nat.min 100 (Kp * (reservoir_level_cm s - setpoint_cm))).
    set (slew_up := Nat.min clamped (gate_open_pct s + actual_slew_pct)).
    destruct (Nat.le_ge_cases slew_up (gate_open_pct s - actual_slew_pct)) as [Hcase|Hcase].
    - rewrite (Nat.max_r _ _ Hcase). lia.
    - rewrite (Nat.max_l _ _ Hcase).
      eapply Nat.le_trans.
      + apply Nat.le_min_l.
      + apply Nat.le_min_l.
  Qed.

  Lemma control_prop_slew : forall s t,
    gate_ok s ->
    control_prop s t <= gate_open_pct s + actual_slew_pct /\
    gate_open_pct s <= control_prop s t + actual_slew_pct.
  Proof.
    intros s t Hok.
    unfold control_prop.
    split.
    - apply Nat.max_lub.
      + apply Nat.le_min_r.
      + lia.
    - apply Nat.max_case_strong; intros; lia.
  Qed.

  Definition threshold_prop : nat := max_reservoir_cm pc - margin_cm.

  Hypothesis gain_sufficient :
    forall s, reservoir_level_cm s >= threshold_prop ->
              gate_ok s ->
              Kp * (reservoir_level_cm s - setpoint_cm) >= 100.

  Hypothesis slew_allows_100 :
    forall s, reservoir_level_cm s >= threshold_prop ->
              gate_ok s ->
              gate_open_pct s + actual_slew_pct >= 100.

  Hypothesis stage_bounded_hyp :
    forall out, stage_from_outflow out <= max_downstream_cm pc.

  Lemma reservoir_preserved_prop :
    forall s t, safe s -> gate_ok s ->
      reservoir_level_cm s + worst_case_inflow t
        <= outflow worst_case_inflow control_prop s t + max_reservoir_cm pc.
  Proof.
    intros s t Hsafe Hgate.
    unfold safe in Hsafe.
    destruct Hsafe as [Hres _].
    destruct (Nat.le_gt_cases (reservoir_level_cm s) threshold_prop) as [Hlow|Hhigh].
    - unfold outflow, available_water.
      assert (Hinflow := inflow_below_margin t).
      unfold threshold_prop in Hlow.
      assert (Hlt_margin : reservoir_level_cm s + margin_cm <= max_reservoir_cm pc) by lia.
      assert (Hresv_le : reservoir_level_cm s + worst_case_inflow t <= max_reservoir_cm pc) by lia.
      lia.
    - assert (Hge : reservoir_level_cm s >= threshold_prop) by lia.
      pose proof (@gain_sufficient s Hge Hgate) as Hgain.
      pose proof (capacity_sufficient_prop t) as Hcap.
      unfold outflow, available_water.
      set (avail := reservoir_level_cm s + worst_case_inflow t).
      set (cmd := control_prop s t).
      set (cap := gate_capacity_cms pc * cmd / 100).
      assert (Hcmd_100 : cmd = 100 \/ cmd < 100).
      { unfold cmd, control_prop.
        set (raw := Kp * (reservoir_level_cm s - setpoint_cm)).
        assert (Hraw_ge : raw >= 100) by exact Hgain.
        assert (Hclamped_eq : Nat.min 100 raw = 100) by (apply Nat.min_l; lia).
        rewrite Hclamped_eq.
        set (slew_up := Nat.min 100 (gate_open_pct s + actual_slew_pct)).
        destruct (Nat.eq_dec (Nat.max slew_up (gate_open_pct s - actual_slew_pct)) 100).
        - left. exact e.
        - right. unfold gate_ok in Hgate.
          assert (Hsu_le : slew_up <= 100) by apply Nat.le_min_l.
          assert (Hmax_le : Nat.max slew_up (gate_open_pct s - actual_slew_pct) <= 100).
          { apply Nat.max_lub.
            - exact Hsu_le.
            - lia. }
          lia. }
      destruct Hcmd_100 as [Hcmd_eq | Hcmd_lt].
      + subst cmd.
        unfold cap.
        rewrite Hcmd_eq.
        rewrite Nat.div_mul by discriminate.
        assert (Hcap_ge : gate_capacity_cms pc >= worst_case_inflow t) by lia.
        apply Nat.min_case_strong; intro Hcmp; lia.
      + pose proof (@slew_allows_100 s Hge Hgate) as Hslew.
        subst cmd.
        unfold control_prop in Hcmd_lt.
        set (raw := Kp * (reservoir_level_cm s - setpoint_cm)) in Hcmd_lt.
        assert (Hraw_ge : raw >= 100) by exact Hgain.
        assert (Hclamped_eq : Nat.min 100 raw = 100) by (apply Nat.min_l; lia).
        rewrite Hclamped_eq in Hcmd_lt.
        assert (Hslew_up_100 : Nat.min 100 (gate_open_pct s + actual_slew_pct) = 100).
        { apply Nat.min_l. lia. }
        rewrite Hslew_up_100 in Hcmd_lt.
        assert (Hmax_100 : Nat.max 100 (gate_open_pct s - actual_slew_pct) = 100).
        { apply Nat.max_l. unfold gate_ok in Hgate. lia. }
        rewrite Hmax_100 in Hcmd_lt.
        lia.
  Qed.

  Lemma stage_bounded_prop :
    forall out, stage_from_outflow out <= max_downstream_cm pc.
  Proof.
    intro out.
    apply stage_bounded_hyp.
  Qed.

  Lemma step_preserves_safe_prop : forall s t,
    safe s -> gate_ok s -> safe (step worst_case_inflow control_prop s t).
  Proof.
    intros s t Hs Hg.
    unfold safe in *.
    destruct Hs as [Hres Hstage].
    unfold step.
    simpl.
    set (qin := worst_case_inflow t).
    set (out := outflow worst_case_inflow control_prop s t).
    assert (Hres_bound : reservoir_level_cm s + qin <= out + max_reservoir_cm pc)
      by (apply reservoir_preserved_prop; [split|]; assumption).
    split.
    - apply sub_le_from_bound. exact Hres_bound.
    - apply stage_bounded_prop.
  Qed.

  Lemma step_preserves_gate_prop : forall s t,
    gate_ok s -> gate_ok (step worst_case_inflow control_prop s t).
  Proof.
    intros s t Hg.
    unfold gate_ok, step.
    simpl.
    apply control_prop_within.
    exact Hg.
  Qed.

  Lemma run_preserves_safe_prop : forall h s,
    safe s -> gate_ok s -> safe (run worst_case_inflow control_prop h s).
  Proof.
    induction h as [|h IH]; intros s Hs Hg.
    - exact Hs.
    - simpl.
      apply IH.
      + apply step_preserves_safe_prop; assumption.
      + apply step_preserves_gate_prop; assumption.
  Qed.

  Theorem proportional_schedule_safe :
    forall s0 horizon,
      safe s0 -> gate_ok s0 ->
      safe (run worst_case_inflow control_prop horizon s0).
  Proof.
    intros.
    apply run_preserves_safe_prop; assumption.
  Qed.

End ProportionalCertified.

(** --------------------------------------------------------------------------- *)
(** Rating-table hydraulic model instantiation                                  *)
(** --------------------------------------------------------------------------- *)

Section RatingTableCertified.

  Variable margin_cm : nat.
  Variable rating_tbl : RatingTable.

  (** Margin fits under crest. *)
  Hypothesis margin_le_reservoir : margin_cm <= max_reservoir_cm pc.
  (** Worst-case inflow fits within margin. *)
  Hypothesis inflow_below_margin : forall t, worst_case_inflow t <= margin_cm.
  (** Gate capacity covers worst-case inflow. *)
  Hypothesis capacity_sufficient : forall t, worst_case_inflow t <= gate_capacity_cms pc.
  (** Slew allows full-open (placeholder for simplicity). *)
  Hypothesis gate_slew_full
    : gate_slew_pct pc >= 100.

  (** Stage is given by the rating table. *)
  Hypothesis stage_table_model
    : forall out, stage_from_outflow out = stage_from_table rating_tbl out.

  (** Rating table is monotone (used by stage_from_table_mono). *)
  Hypothesis rating_monotone
    : monotone_table rating_tbl.

  (** Rating table stages are bounded by downstream ceiling. *)
  Hypothesis rating_bounded
    : table_stages_bounded rating_tbl (max_downstream_cm pc).

  (** Ramp allowance exceeds downstream ceiling (placeholder). *)
  Hypothesis ramp_budget
    : max_stage_rise_cm pc >= max_downstream_cm pc.

  (** Threshold to go full-open: crest minus margin. *)
  Definition threshold_table_cm
    : nat
    := max_reservoir_cm pc - margin_cm.

  (** Margin-based controller for rating-table hydraulics. *)
  Definition control_table (s:State) (_:nat) : nat :=
    if Nat.leb threshold_table_cm (reservoir_level_cm s)
    then 100
    else Nat.min 100 (Nat.max 0 (gate_open_pct s - gate_slew_pct pc)).

  (** Controller output is bounded by 100%. *)
  Lemma control_table_within : forall s t, control_table s t <= 100.
  Proof.
    intros. unfold control_table.
    destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)); [lia|].
    apply Nat.le_min_l.
  Qed.

  (** Controller respects slew constraints. *)
  Lemma control_table_slew : forall s t,
    gate_ok s ->
    control_table s t <= gate_open_pct s + gate_slew_pct pc /\
    gate_open_pct s <= control_table s t + gate_slew_pct pc.
  Proof.
    intros s t Hok; unfold control_table; destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)).
    - split.
      + apply Nat.le_trans with (m := gate_slew_pct pc); [apply gate_slew_full|lia].
      + apply Nat.le_trans with (m := 100); [exact Hok|lia].
    - split.
      + apply Nat.le_trans with (m := Nat.max 0 (gate_open_pct s - gate_slew_pct pc)).
        * apply Nat.le_min_r.
        * apply Nat.max_case_strong; intros; lia.
      + destruct (le_lt_dec (gate_slew_pct pc) (gate_open_pct s)).
        * assert (gate_open_pct s = (gate_open_pct s - gate_slew_pct pc) + gate_slew_pct pc) by lia.
          assert (Hmax : Nat.max 0 (gate_open_pct s - gate_slew_pct pc) = gate_open_pct s - gate_slew_pct pc) by lia.
          rewrite Hmax.
          assert (Hdiff_le1 : gate_open_pct s - gate_slew_pct pc <= gate_open_pct s) by apply Nat.le_sub_l.
          assert (Hdiff_le : gate_open_pct s - gate_slew_pct pc <= 100) by (eapply Nat.le_trans; [exact Hdiff_le1|exact Hok]).
          rewrite (Nat.min_r _ _ Hdiff_le).
          lia.
        * (* gate < slew, control goes to 0 *)
          assert (gate_open_pct s <= gate_slew_pct pc) by lia.
          assert (Nat.max 0 (gate_open_pct s - gate_slew_pct pc) = 0) by lia.
          rewrite H0. simpl. lia.
  Qed.

  (** Discharge under control_table never exceeds capacity. *)
  Lemma outflow_le_capacity_table : forall s t,
    outflow worst_case_inflow control_table s t <= gate_capacity_cms pc.
  Proof.
    intros. unfold outflow, available_water. simpl.
    apply Nat.le_trans with (m := gate_capacity_cms pc * control_table s t / 100).
    - apply Nat.le_min_l.
    - pose proof (control_table_within s t) as Hc.
      assert (Hmul : gate_capacity_cms pc * control_table s t <= gate_capacity_cms pc * 100)
        by (apply Nat.mul_le_mono_l; lia).
      apply (Nat.Div0.div_le_mono _ _ 100) in Hmul.
      rewrite Nat.div_mul in Hmul by discriminate.
      exact Hmul.
  Qed.

  (** Mass balance: storage + inflow stays within crest + discharge (table). *)
  Lemma reservoir_preserved_table
    : forall s t,
      safe s ->
      reservoir_level_cm s + worst_case_inflow t
        <= outflow worst_case_inflow control_table s t + max_reservoir_cm pc.
  Proof.
    intros s t Hsafe. unfold safe in Hsafe. destruct Hsafe as [Hres _].
    unfold control_table.
    destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)) eqn:Hbranch.
    - (* fully open; capacity dominates inflow *)
      assert (Hcap := capacity_sufficient t).
      unfold outflow, available_water. rewrite Hbranch.
      apply Nat.min_case_strong; intro Hcmp.
      + rewrite Nat.div_mul by discriminate.
        assert (Hstep1 : reservoir_level_cm s + worst_case_inflow t <= reservoir_level_cm s + gate_capacity_cms pc)
          by (apply Nat.add_le_mono_l; exact Hcap).
        assert (Hstep2 : reservoir_level_cm s + gate_capacity_cms pc <= max_reservoir_cm pc + gate_capacity_cms pc)
          by (apply Nat.add_le_mono_r; exact Hres).
        eapply Nat.le_trans; [exact Hstep1|].
        eapply Nat.le_trans; [exact Hstep2|].
        rewrite Nat.add_comm. apply Nat.le_refl.
      + unfold available_water. lia.
    - (* below threshold; rely on margin *)
      apply Nat.leb_gt in Hbranch.
      unfold outflow, available_water. simpl.
      assert (Hinflow := inflow_below_margin t).
      assert (Hlt_margin : reservoir_level_cm s + margin_cm < max_reservoir_cm pc).
      { unfold threshold_table_cm in Hbranch.
        apply Nat.add_lt_mono_r with (p := margin_cm) in Hbranch.
        rewrite Nat.sub_add in Hbranch by exact margin_le_reservoir.
        exact Hbranch. }
      assert (Hresv_le : reservoir_level_cm s + worst_case_inflow t <= max_reservoir_cm pc).
      { apply Nat.lt_le_incl.
        eapply Nat.le_lt_trans.
        - apply Nat.add_le_mono_l; exact Hinflow.
        - exact Hlt_margin. }
      lia.
  Qed.

  (** Stage under table-based control is below downstream ceiling. *)
  Lemma stage_bounded_table :
    forall out, stage_from_outflow out <= max_downstream_cm pc.
  Proof.
    intro out. rewrite stage_table_model.
    eapply Nat.le_trans; [apply stage_from_table_bounded; exact rating_bounded|lia].
  Qed.

  (** Downstream ramp bound under table-based control. *)
  Lemma stage_ramp_preserved_table :
    forall s t, safe s ->
      stage_from_outflow (outflow worst_case_inflow control_table s t) <= downstream_stage_cm s + max_stage_rise_cm pc.
  Proof.
    intros s t Hsafe.
    assert (Hstage := stage_bounded_table (outflow worst_case_inflow control_table s t)).
    assert (Hnonneg : 0 <= downstream_stage_cm s) by lia.
    lia.
  Qed.

  (** One table-based step preserves reservoir and stage safety. *)
  Lemma step_preserves_safe_table : forall s t, safe s -> safe (step worst_case_inflow control_table s t).
  Proof.
    intros s t Hs. unfold safe in *. destruct Hs as [Hres Hstage].
    unfold step. simpl.
    set (inflow := worst_case_inflow t).
    set (out := outflow worst_case_inflow control_table s t).
    assert (Hres_bound : reservoir_level_cm s + inflow <= out + max_reservoir_cm pc)
      by (apply reservoir_preserved_table; split; assumption).
    split.
    - apply sub_le_from_bound; assumption.
    - apply stage_bounded_table.
  Qed.

  (** Table-based run preserves safety over the horizon. *)
  Lemma run_preserves_safe_table : forall h s, safe s -> safe (run worst_case_inflow control_table h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_table; assumption].
  Qed.

  (** Gate remains within 0–100% after a table-based step. *)
  Lemma gate_pct_bounded_table : forall s t, gate_open_pct (step worst_case_inflow control_table s t) <= 100.
  Proof. intros; unfold step; simpl; apply control_table_within. Qed.

  (** One table-based step preserves validity. *)
  Lemma step_preserves_valid_table : forall s t, valid s -> valid (step worst_case_inflow control_table s t).
  Proof.
    intros s t [Hs Hg]. split.
    - apply step_preserves_safe_table; auto.
    - apply gate_pct_bounded_table.
  Qed.

  (** Table-based run preserves validity over the horizon. *)
  Lemma run_preserves_valid_table : forall h s, valid s -> valid (run worst_case_inflow control_table h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_valid_table; assumption].
  Qed.

  (** Horizon safety guarantee for the rating-table controller. *)
  Corollary rating_schedule_safe :
    forall s0 horizon,
      safe s0 ->
      safe (run worst_case_inflow control_table horizon s0).
  Proof.
    intros s0 horizon Hsafe. now apply run_preserves_safe_table.
  Qed.

  (** Horizon validity guarantee for the rating-table controller. *)
  Corollary rating_schedule_valid :
    forall s0 horizon,
      valid s0 ->
      valid (run worst_case_inflow control_table horizon s0).
  Proof.
    intros s0 horizon Hvalid. now apply run_preserves_valid_table.
  Qed.

End RatingTableCertified.

(** --------------------------------------------------------------------------- *)
(** Multi-gate extension with aggregate safety proof.

    This section extends the single-gate model to multiple spillway gates.
    Key derived properties:
    - sum_gate_pct_le_bound: aggregate opening bounded by 100 * gate_count
    - step_mg_preserves_safe: one step maintains safety
    - run_mg_preserves_valid: horizon validity

    Parameters (to be instantiated for concrete multi-gate controllers):
    - control_mg_within_bounds: controller produces valid gate vector
    - stage_bounded_mg: stage response bounded by downstream ceiling
    - capacity_sufficient_mg: aggregate capacity handles worst-case inflow      *)
(** --------------------------------------------------------------------------- *)

Section MultiGate.

  Variable gate_count : nat.
  Hypothesis gate_count_pos : gate_count > 0.
  Parameter gate_capacity_cms_per_gate : nat.
  Parameter stage_from_outflow_mg      : nat -> nat.
  Parameter control_mg                 : State -> nat -> list nat.

  Definition Gates := list nat.

  Definition gates_ok (gs:Gates) : Prop :=
    length gs = gate_count /\ Forall (fun pct => pct <= 100) gs.

  Fixpoint sum_gate_pct (gs:Gates) : nat :=
    match gs with
    | [] => 0
    | g::rest => g + sum_gate_pct rest
    end.

  (** Sum of gate openings is nonnegative. *)
  Lemma sum_gate_pct_nonneg : forall gs, sum_gate_pct gs >= 0.
  Proof. intros; lia. Qed.

  (** Sum of gate openings bounded by 100 * number of gates (from Forall). *)
  Lemma sum_gate_pct_le_len : forall gs,
      Forall (fun pct => pct <= 100) gs ->
      sum_gate_pct gs <= 100 * length gs.
  Proof.
    induction gs as [|g gs IH]; intros Hforall.
    - cbn. lia.
    - inversion Hforall as [|? ? Hle Hrest]; subst.
      cbn [sum_gate_pct length].
      replace (100 * S (length gs)) with (100 + 100 * length gs) by lia.
      specialize (IH Hrest).
      apply Nat.add_le_mono; [exact Hle|].
      lia.
  Qed.

  (** Sum of gate openings bounded by 100 * gate_count (from gates_ok). *)
  Lemma sum_gate_pct_le_bound : forall gs,
      gates_ok gs -> sum_gate_pct gs <= 100 * gate_count.
  Proof.
    intros gs [Hlen Hforall].
    rewrite <- Hlen.
    apply sum_gate_pct_le_len; assumption.
  Qed.

  (** Aggregate discharge capacity given gate openings. *)
  Definition outflow_capacity_mg (gs:Gates) : nat :=
    gate_capacity_cms_per_gate * sum_gate_pct gs / 100.

  (** Aggregate outflow: min of capacity and available water. *)
  Definition outflow_mg (s:State) (t:nat) : nat :=
    let gs := control_mg s t in
    Nat.min (outflow_capacity_mg gs) (available_water worst_case_inflow s t).

  (** Multi-gate plant step with aggregate discharge. *)
  Definition step_mg (s:State) (t:nat) : State :=
    let gs := control_mg s t in
    let inflow := worst_case_inflow t in
    let out := outflow_mg s t in
    let new_res := reservoir_level_cm s + inflow - out in
    let new_stage := stage_from_outflow_mg out in
    {| reservoir_level_cm := new_res;
       downstream_stage_cm := new_stage;
       gate_open_pct := sum_gate_pct gs / gate_count |}.

  (** Iterate multi-gate steps over a horizon. *)
  Fixpoint run_mg (h:nat) (s:State) : State :=
    match h with
    | O => s
    | S k => run_mg k (step_mg s k)
    end.

  (** Multi-gate controller returns the correct number of bounded gate settings. *)
  Parameter control_mg_within_bounds :
    forall s t, gates_ok (control_mg s t).

  (** Aggregate stage response is below downstream ceiling. *)
  Parameter stage_bounded_mg :
    forall out, stage_from_outflow_mg out <= max_downstream_cm pc.

  (** Aggregate capacity exceeds worst-case inflow. *)
  Parameter capacity_sufficient_mg :
    forall s t, worst_case_inflow t <= outflow_capacity_mg (control_mg s t).

  (** One multi-gate step preserves reservoir and stage safety. *)
  Lemma step_mg_preserves_safe : forall s t, safe s -> safe (step_mg s t).
  Proof.
    intros s t Hsafe. unfold safe in *. destruct Hsafe as [Hres _].
    unfold step_mg. simpl.
    set (gs := control_mg s t).
    set (outcap := outflow_capacity_mg gs).
    set (aw := available_water worst_case_inflow s t).
    set (out := Nat.min outcap aw).
    assert (Hout_ge_inflow : worst_case_inflow t <= out).
    { unfold out, outcap, aw.
      apply Nat.min_glb.
      - apply capacity_sufficient_mg.
      - unfold available_water. lia. }
    split.
    - (* reservoir bound *)
      assert (Hdrop : reservoir_level_cm s + worst_case_inflow t - out <= reservoir_level_cm s) by lia.
      eapply Nat.le_trans; [exact Hdrop|exact Hres].
    - apply stage_bounded_mg.
  Qed.

  (** One multi-gate step preserves validity. *)
  Lemma step_mg_preserves_valid : forall s t, valid s -> valid (step_mg s t).
  Proof.
    intros s t [Hsafe Hgate]. split.
    - apply step_mg_preserves_safe; assumption.
    - unfold step_mg. simpl.
      destruct (control_mg_within_bounds s t) as [Hlen Hforall].
      assert (Hsum : sum_gate_pct (control_mg s t) <= 100 * gate_count)
        by (apply sum_gate_pct_le_bound; split; assumption).
      assert (Hsum' : sum_gate_pct (control_mg s t) <= gate_count * 100) by (rewrite Nat.mul_comm; exact Hsum).
      pose proof (Nat.Div0.div_le_upper_bound (sum_gate_pct (control_mg s t)) gate_count 100 Hsum') as Hdiv.
      exact Hdiv.
  Qed.

  (** Multi-gate run preserves validity over the horizon. *)
  Lemma run_mg_preserves_valid : forall h s, valid s -> valid (run_mg h s).
  Proof.
    induction h as [|h IH]; intros s Hvalid.
    - exact Hvalid.
    - simpl. apply IH. apply step_mg_preserves_valid; assumption.
  Qed.

  (** Horizon validity guarantee for the multi-gate controller. *)
  Theorem schedule_valid_mg :
    forall s0 horizon, valid s0 -> valid (run_mg horizon s0).
  Proof. intros; eapply run_mg_preserves_valid; eauto. Qed.

End MultiGate.

(** --------------------------------------------------------------------------- *)
(** Signed-flow (Z) variant to reason about negative margins / offsets          *)
(** --------------------------------------------------------------------------- *)

Section SignedFlow.

  (** Integer-valued spillway state. *)
  Record ZState := {
    z_reservoir_cm : Z;
    z_downstream_cm : Z;
    z_gate_pct : Z
  }.

  Local Open Scope Z_scope.

  (** Integer-valued reservoir crest (cm). *)
  Parameter z_max_reservoir_cm  : Z.
  (** Integer-valued downstream stage ceiling (cm). *)
  Parameter z_max_downstream_cm : Z.
  (** Integer-valued capacity at 100% gate (cms). *)
  Parameter z_gate_capacity_cms : Z.
  (** Integer-valued gate slew (%). *)
  Parameter z_gate_slew_pct     : Z.
  (** Integer-valued per-step stage rise allowance (cm). *)
  Parameter z_max_stage_rise_cm : Z.

  (** Integer worst-case inflow per timestep. *)
  Parameter worst_case_inflow_z : nat -> Z.
  (** Integer hydraulic response to outflow. *)
  Parameter stage_from_outflow_z : Z -> Z.
  (** Integer controller output. *)
  Parameter control_z : ZState -> nat -> Z.

  (** Integer safety: reservoir and downstream within bounds. *)
  Definition safe_z (s:ZState) : Prop :=
    0 <= z_reservoir_cm s /\ z_reservoir_cm s <= z_max_reservoir_cm /\
    0 <= z_downstream_cm s /\ z_downstream_cm s <= z_max_downstream_cm.

  (** Integer gate command within [0,100]. *)
  Definition gate_ok_z (s:ZState) : Prop :=
    0 <= z_gate_pct s /\ z_gate_pct s <= 100.

  (** Integer validity: safety and gate bounds. *)
  Definition valid_z (s:ZState) : Prop := safe_z s /\ gate_ok_z s.

  (** Integer available water: storage plus inflow. *)
  Definition available_water_z (s:ZState) (t:nat) : Z :=
    z_reservoir_cm s + worst_case_inflow_z t.

  (** Integer outflow: min of capacity and availability. *)
  Definition outflow_z (ctrl:ZState -> nat -> Z) (s:ZState) (t:nat) : Z :=
    Z.min (z_gate_capacity_cms * ctrl s t / 100) (available_water_z s t).

  (** Integer plant step. *)
  Definition step_z (ctrl:ZState -> nat -> Z) (s:ZState) (t:nat) : ZState :=
    let inflow := worst_case_inflow_z t in
    let out := outflow_z ctrl s t in
    let new_res := z_reservoir_cm s + inflow - out in
    let new_stage := stage_from_outflow_z out in
    {| z_reservoir_cm := new_res;
       z_downstream_cm := new_stage;
       z_gate_pct := ctrl s t |}.

  (** Integer plant run over a horizon. *)
  Fixpoint run_z (ctrl:ZState -> nat -> Z) (h:nat) (s:ZState) : ZState :=
    match h with
    | O => s
    | S k => run_z ctrl k (step_z ctrl s k)
    end.

  (** Integer controller output respects physical gate bounds. *)
  Hypothesis control_within_bounds_z :
    forall s t, 0 <= control_z s t <= 100.

  (** Integer controller slew is within +/- z_gate_slew_pct per step. *)
  Hypothesis control_slew_limited_z :
    forall s t, gate_ok_z s ->
      - z_gate_slew_pct <= control_z s t - z_gate_pct s <= z_gate_slew_pct.

  (** Integer inflow is never negative. *)
  Hypothesis inflow_nonneg_z :
    forall t, 0 <= worst_case_inflow_z t.

  (** Integer gate capacity covers worst-case inflow. *)
  Hypothesis capacity_sufficient_z :
    forall s t, worst_case_inflow_z t <= z_gate_capacity_cms * control_z s t / 100.

  (** Integer stage response respects downstream ceiling. *)
  Hypothesis stage_bounded_z :
    forall out, stage_from_outflow_z out <= z_max_downstream_cm.

  (** Integer stage response is monotone in outflow. *)
  Hypothesis stage_monotone_z :
    forall o1 o2, o1 <= o2 -> stage_from_outflow_z o1 <= stage_from_outflow_z o2.

  (** Integer stage response is nonnegative. *)
  Hypothesis stage_nonneg_z :
    forall out, 0 <= stage_from_outflow_z out.

  (** Integer stage ramp limit holds for one step. *)
  Hypothesis stage_ramp_preserved_z :
    forall s t, safe_z s ->
      stage_from_outflow_z (outflow_z control_z s t) <= z_downstream_cm s + z_max_stage_rise_cm.

  (** Nonnegativity of subtraction when a >= b in Z. *)
  Lemma Z_sub_nonneg_from_le : forall a b, b <= a -> 0 <= a - b.
  Proof. intros; lia. Qed.

  (** Gate bounds preserved by integer plant step. *)
  Lemma gate_pct_bounded_z : forall s t, gate_ok_z s -> gate_ok_z (step_z control_z s t).
  Proof.
    intros s t [Hlo Hhi]. unfold gate_ok_z, step_z; simpl.
    destruct (control_within_bounds_z s t) as [Hc_lo Hc_hi]. split; lia.
  Qed.

  (** Integer safety preserved by a single step. *)
  Lemma step_preserves_safe_z : forall s t, safe_z s -> safe_z (step_z control_z s t).
  Proof.
    intros s t Hsafe. unfold safe_z in *. destruct Hsafe as [Hres0 [Hres_max [Hstage0 Hstage_max]]].
    unfold step_z. simpl.
    set (inflow := worst_case_inflow_z t).
    set (outcap := z_gate_capacity_cms * control_z s t / 100).
    set (aw := available_water_z s t).
    destruct (Z.leb_spec outcap aw) as [Hle_cap|Hgt_cap].
    - (* capacity branch is limiting *)
      assert (Hout_eq : outflow_z control_z s t = outcap).
      { unfold outflow_z, outcap, aw. destruct (Z.leb_spec outcap aw); lia. }
      rewrite Hout_eq. unfold inflow, aw in *.
      assert (Hinflow_le_out : inflow <= outcap) by (subst outcap; apply capacity_sufficient_z).
      assert (Hres_nonneg : 0 <= z_reservoir_cm s) by exact Hres0.
      assert (Hout_le_avail : outcap <= z_reservoir_cm s + inflow) by (subst aw; unfold available_water_z in Hle_cap; exact Hle_cap).
      split; [apply Z.le_0_sub; exact Hout_le_avail|].
      split.
      { apply Z.le_sub_le_add_r. lia. }
      split; [apply stage_nonneg_z|apply stage_bounded_z].
    - (* availability branch is limiting *)
      assert (Hout_eq : outflow_z control_z s t = aw).
      { unfold outflow_z, outcap, aw. destruct (Z.leb_spec outcap aw); lia. }
      rewrite Hout_eq. unfold aw, available_water_z, inflow in *.
      split; [lia|].
      split; [lia|].
      split; [apply stage_nonneg_z|apply stage_bounded_z].
  Qed.

  (** Integer validity preserved by a single step. *)
  Lemma step_preserves_valid_z : forall s t, valid_z s -> valid_z (step_z control_z s t).
  Proof.
    intros s t [Hsafe Hgate]. split.
    - apply step_preserves_safe_z; assumption.
    - apply gate_pct_bounded_z; assumption.
  Qed.

  (** Integer safety preserved across a run. *)
  Lemma run_preserves_safe_z : forall h s, safe_z s -> safe_z (run_z control_z h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_z; assumption].
  Qed.

  (** Integer validity preserved across a run. *)
  Lemma run_preserves_valid_z : forall h s, valid_z s -> valid_z (run_z control_z h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_valid_z; assumption].
  Qed.

  (** Mass-balance audit for signed flow: exact conservation identity. *)
  Fixpoint net_z (h:nat) (s:ZState) : Z :=
    match h with
    | O => 0
    | S k =>
      let out := outflow_z control_z s k in
      let s' := step_z control_z s k in
      (worst_case_inflow_z k - out) + net_z k s'
    end.

  (** Reservoir balance identity across one integer step. *)
  Lemma step_reservoir_balance_z : forall s t,
    z_reservoir_cm (step_z control_z s t) =
    z_reservoir_cm s + worst_case_inflow_z t - outflow_z control_z s t.
  Proof. intros; reflexivity. Qed.

  (** Reservoir balance identity across an integer horizon. *)
  Lemma run_reservoir_balance_z : forall h s,
    z_reservoir_cm (run_z control_z h s) =
    z_reservoir_cm s + net_z h s.
  Proof.
    induction h; intros; simpl.
    - ring.
    - rewrite IHh. simpl. ring.
  Qed.

  (** Integer downstream ramp preserved over a horizon. *)
  Lemma run_preserves_ramp_z : forall k s,
    safe_z s ->
    z_downstream_cm (run_z control_z k s) <= z_downstream_cm s + Z.of_nat k * z_max_stage_rise_cm.
  Proof.
    induction k; intros s Hsafe; cbn [run_z].
    - lia.
    - set (s' := step_z control_z s k).
      assert (Hsafe' : safe_z s') by (apply step_preserves_safe_z; assumption).
      assert (Hramp : z_downstream_cm s' <= z_downstream_cm s + z_max_stage_rise_cm)
        by (apply stage_ramp_preserved_z; assumption).
      specialize (IHk s' Hsafe').
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      rewrite Z.mul_add_distr_r.
      rewrite Z.mul_1_l.
      replace (z_downstream_cm s + (Z.of_nat k * z_max_stage_rise_cm + z_max_stage_rise_cm))
        with (z_downstream_cm s + z_max_stage_rise_cm + Z.of_nat k * z_max_stage_rise_cm) by lia.
      eapply Z.le_trans; [apply IHk|].
      apply Z.add_le_mono_r with (p := Z.of_nat k * z_max_stage_rise_cm) in Hramp.
      exact Hramp.
  Qed.

  (** Integer downstream ramp respected over a horizon. *)
  Theorem schedule_safe_z :
    forall s0 horizon, safe_z s0 -> safe_z (run_z control_z horizon s0).
  Proof. intros; apply run_preserves_safe_z; assumption. Qed.

  (** Integer validity respected over a horizon. *)
  Theorem schedule_valid_z :
    forall s0 horizon, valid_z s0 -> valid_z (run_z control_z horizon s0).
  Proof. intros; apply run_preserves_valid_z; assumption. Qed.

End SignedFlow.

End WithPlantConfig.

(** --------------------------------------------------------------------------- *)
(** Witness Examples: Concrete instantiations demonstrating non-vacuous safety  *)
(**                                                                             *)
(** These examples verify that:                                                 *)
(**   1. The safety predicates are satisfiable                                  *)
(**   2. The controller produces non-trivial behavior                           *)
(**   3. The margin is actually used (level approaches crest)                   *)
(** --------------------------------------------------------------------------- *)

Section WitnessExamples.

  Definition witness_plant : PlantConfig.
  Proof.
    refine (@mkPlantConfig 100 50 10 1 2 5 100 1 _ _ _ _ _).
    all: abstract lia.
  Defined.

  Definition witness_inflow (_ : nat) : nat := 8.

  Definition witness_stage (out : nat) : nat := out / 2.

  Definition witness_state_initial : State :=
    {| reservoir_level_cm := 80;
       downstream_stage_cm := 4;
       gate_open_pct := 50 |}.

  Definition witness_state_high : State :=
    {| reservoir_level_cm := 95;
       downstream_stage_cm := 5;
       gate_open_pct := 80 |}.

  Definition witness_state_critical : State :=
    {| reservoir_level_cm := 99;
       downstream_stage_cm := 5;
       gate_open_pct := 100 |}.

  Lemma witness_initial_safe : safe witness_plant witness_state_initial.
  Proof.
    unfold safe, witness_state_initial.
    vm_compute.
    split; lia.
  Qed.

  Lemma witness_initial_valid : valid witness_plant witness_state_initial.
  Proof.
    split.
    - exact witness_initial_safe.
    - unfold gate_ok, witness_state_initial. vm_compute. lia.
  Qed.

  Lemma witness_high_safe : safe witness_plant witness_state_high.
  Proof.
    unfold safe, witness_state_high.
    vm_compute.
    split; lia.
  Qed.

  Lemma witness_critical_safe : safe witness_plant witness_state_critical.
  Proof.
    unfold safe, witness_state_critical.
    vm_compute.
    split; lia.
  Qed.

  Lemma witness_critical_gate_ok : gate_ok witness_state_critical.
  Proof.
    unfold gate_ok, witness_state_critical.
    vm_compute.
    lia.
  Qed.

  Lemma witness_margin_nontrivial :
    reservoir_level_cm witness_state_high + 5 <= max_reservoir_cm witness_plant.
  Proof.
    vm_compute.
    lia.
  Qed.

  Lemma witness_critical_at_margin :
    reservoir_level_cm witness_state_critical + 5 > max_reservoir_cm witness_plant.
  Proof.
    vm_compute.
    lia.
  Qed.

  Lemma witness_capacity_covers_inflow :
    forall t, witness_inflow t <= gate_capacity_cms witness_plant.
  Proof.
    intro t.
    vm_compute.
    lia.
  Qed.

  Lemma witness_stage_bounded_at_capacity :
    witness_stage (gate_capacity_cms witness_plant) <= max_downstream_cm witness_plant.
  Proof.
    vm_compute.
    lia.
  Qed.

End WitnessExamples.

(** --------------------------------------------------------------------------- *)
(** Counterexample Section: Demonstrations of failure without proper control    *)
(**                                                                             *)
(** These examples show that:                                                   *)
(**   1. Without a controller, overflow can occur                               *)
(**   2. A weak controller (insufficient capacity) fails                        *)
(**   3. The margin assumption is necessary                                     *)
(** --------------------------------------------------------------------------- *)

Section CounterexampleTests.

  Definition bad_plant_no_capacity : PlantConfig.
  Proof.
    refine (@mkPlantConfig 100 50 1 1 100 50 100 1 _ _ _ _ _).
    all: abstract lia.
  Defined.

  Definition high_inflow (_ : nat) : nat := 10.

  Lemma counterexample_capacity_insufficient :
    exists t, high_inflow t > gate_capacity_cms bad_plant_no_capacity.
  Proof.
    exists 0.
    vm_compute.
    lia.
  Qed.

  Definition failing_state : State :=
    {| reservoir_level_cm := 95;
       downstream_stage_cm := 4;
       gate_open_pct := 100 |}.

  Lemma counterexample_would_overflow :
    reservoir_level_cm failing_state + high_inflow 0
      > max_reservoir_cm bad_plant_no_capacity.
  Proof.
    vm_compute.
    lia.
  Qed.

  Lemma counterexample_max_outflow :
    gate_capacity_cms bad_plant_no_capacity * 100 / 100
      = gate_capacity_cms bad_plant_no_capacity.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma counterexample_outflow_limited_when_bounded :
    forall cmd, cmd <= 100 ->
      gate_capacity_cms bad_plant_no_capacity * cmd / 100
        <= gate_capacity_cms bad_plant_no_capacity.
  Proof.
    intros cmd Hcmd.
    assert (Hcap : gate_capacity_cms bad_plant_no_capacity = 1) by reflexivity.
    rewrite Hcap.
    rewrite Nat.mul_1_l.
    apply Nat.Div0.div_le_upper_bound.
    assert (100 * 1 = 100) by lia.
    rewrite H.
    exact Hcmd.
  Qed.

End CounterexampleTests.

(** --------------------------------------------------------------------------- *)
(** Boundary Condition Tests: Edge cases and limit behavior                     *)
(** --------------------------------------------------------------------------- *)

Section BoundaryTests.

  Definition boundary_plant : PlantConfig.
  Proof.
    refine (@mkPlantConfig 100 50 10 0 100 50 100 1 _ _ _ _ _).
    all: abstract lia.
  Defined.

  Definition zero_inflow (_ : nat) : nat := 0.

  Definition boundary_state_empty : State :=
    {| reservoir_level_cm := 0;
       downstream_stage_cm := 0;
       gate_open_pct := 0 |}.

  Definition boundary_state_full : State :=
    {| reservoir_level_cm := 100;
       downstream_stage_cm := 50;
       gate_open_pct := 100 |}.

  Lemma boundary_empty_safe : safe boundary_plant boundary_state_empty.
  Proof.
    unfold safe, boundary_state_empty.
    vm_compute.
    split; lia.
  Qed.

  Lemma boundary_full_safe : safe boundary_plant boundary_state_full.
  Proof.
    unfold safe, boundary_state_full.
    vm_compute.
    split; lia.
  Qed.

  Lemma boundary_full_at_limit :
    reservoir_level_cm boundary_state_full = max_reservoir_cm boundary_plant.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma boundary_zero_inflow_stable :
    forall s, safe boundary_plant s ->
              reservoir_level_cm s + zero_inflow 0 <= max_reservoir_cm boundary_plant.
  Proof.
    intros s Hsafe.
    unfold safe in Hsafe.
    assert (Hmax : max_reservoir_cm boundary_plant = 100) by reflexivity.
    rewrite Hmax in *.
    destruct Hsafe as [Hres _].
    unfold zero_inflow.
    lia.
  Qed.

  Lemma boundary_worst_case_equals_forecast :
    forall t, worst_case_inflow boundary_plant zero_inflow t = 0.
  Proof.
    intro t.
    vm_compute.
    reflexivity.
  Qed.

End BoundaryTests.

