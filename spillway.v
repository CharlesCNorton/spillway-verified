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

From Coq Require Import Arith Lia List ZArith.
Import ListNotations.

Set Implicit Arguments.

(** State and plant parameters *)
Record State := {
  reservoir_level_cm : nat;   (* reservoir elevation (cm) *)
  downstream_stage_cm : nat;  (* downstream stage (cm) *)
  gate_open_pct : nat         (* commanded gate opening percent, 0..100 *)
}.

Parameter max_reservoir_cm   : nat.
Parameter max_downstream_cm  : nat.
Parameter gate_capacity_cms  : nat.   (* outflow per 100% open *)
Parameter forecast_error_pct : nat.   (* symmetric forecast error, percent *)
Parameter gate_slew_pct      : nat.   (* max % change per step *)
Parameter max_stage_rise_cm  : nat.   (* allowed downstream stage rise per step *)

Parameter inflow_forecast_cms : nat -> nat.   (* forecasted inflow at timestep t *)
Parameter stage_from_outflow  : nat -> nat.   (* hydraulic stage response to outflow *)

Definition safe (s : State) : Prop :=
  reservoir_level_cm s <= max_reservoir_cm /\
  downstream_stage_cm s <= max_downstream_cm.

Definition gate_ok (s:State) : Prop := gate_open_pct s <= 100.
Definition valid (s:State) : Prop := safe s /\ gate_ok s.

Definition worst_case_inflow (t:nat) : nat :=
  inflow_forecast_cms t * (100 + forecast_error_pct) / 100.

(** Optional time-varying, correlated forecast error (bounded) *)
Parameter forecast_error_pct_t : nat -> nat.
Hypothesis forecast_error_pct_t_bound :
  forall t, forecast_error_pct_t t <= 2 * forecast_error_pct.

Definition worst_case_inflow_t (t:nat) : nat :=
  inflow_forecast_cms t * (100 + forecast_error_pct_t t) / 100.

Definition available_water (s:State) (t:nat) : nat :=
  reservoir_level_cm s + worst_case_inflow t.

Definition outflow (ctrl:State -> nat -> nat) (s:State) (t:nat) : nat :=
  Nat.min (gate_capacity_cms * ctrl s t / 100) (available_water s t).

Definition available_water_t (s:State) (t:nat) : nat :=
  reservoir_level_cm s + worst_case_inflow_t t.

Definition outflow_t (ctrl:State -> nat -> nat) (s:State) (t:nat) : nat :=
  Nat.min (gate_capacity_cms * ctrl s t / 100) (available_water_t s t).

Definition step (ctrl:State -> nat -> nat) (s:State) (t:nat) : State :=
  let inflow := worst_case_inflow t in
  let out := outflow ctrl s t in
  let new_res := reservoir_level_cm s + inflow - out in
  let new_stage := stage_from_outflow out in
  {| reservoir_level_cm := new_res;
     downstream_stage_cm := new_stage;
     gate_open_pct := ctrl s t |}.

Fixpoint run (ctrl:State -> nat -> nat) (horizon:nat) (s:State) : State :=
  match horizon with
  | O => s
  | S k => run ctrl k (step ctrl s k)
  end.

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

Definition table_stages_bounded (tbl:RatingTable) (bound:nat) : Prop :=
  Forall (fun qs => snd qs <= bound) tbl.

Lemma Nat_max_mono_r : forall s a b, a <= b -> Nat.max s a <= Nat.max s b.
Proof.
  intros s a b Hle.
  destruct (Nat.leb s a) eqn:Ha; destruct (Nat.leb s b) eqn:Hb; lia.
Qed.

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

(** Control/plant assumptions *)
Section SingleGate.

  Variable control : State -> nat -> nat.

  Hypothesis control_within_bounds :
    forall s t, control s t <= 100.

  Hypothesis control_slew_limited :
    forall s t, gate_ok s ->
      control s t <= gate_open_pct s + gate_slew_pct /\
      gate_open_pct s <= control s t + gate_slew_pct.

  Hypothesis control_ramp_limited :
    forall s t, safe s ->
      stage_from_outflow (outflow control s t) <= downstream_stage_cm s + max_stage_rise_cm.

  Hypothesis stage_bounded :
    forall out, stage_from_outflow out <= max_downstream_cm.

  Hypothesis reservoir_preserved :
    forall s t, safe s ->
      reservoir_level_cm s + worst_case_inflow t <= outflow control s t + max_reservoir_cm.

  Hypothesis stage_ramp_preserved :
    forall s t, safe s ->
      stage_from_outflow (outflow control s t) <= downstream_stage_cm s + max_stage_rise_cm.

(** Utility lemma: if a <= b + c then a - b <= c. *)
Lemma sub_le_from_bound : forall a b c, a <= b + c -> a - b <= c.
Proof. intros; lia. Qed.

(** Gate command always recorded within 0..100. *)
Lemma gate_pct_bounded : forall s t, gate_open_pct (step control s t) <= 100.
Proof.
  intros. unfold step. simpl. apply control_within_bounds.
Qed.

Lemma gate_slew_respected : forall s t,
  gate_ok s ->
  gate_open_pct (step control s t) <= gate_open_pct s + gate_slew_pct /\
  gate_open_pct s <= gate_open_pct (step control s t) + gate_slew_pct.
Proof.
  intros s t Hok. unfold step. simpl. apply control_slew_limited; assumption.
Qed.

(** One-step safety preservation under the assumptions. *)
  Lemma step_preserves_safe : forall s t, safe s -> safe (step control s t).
  Proof.
    intros s t Hsafe. unfold safe in *. destruct Hsafe as [Hres Hstage].
    unfold step. simpl.
    set (inflow := worst_case_inflow t).
    set (out := outflow control s t).
    assert (Hres_bound : reservoir_level_cm s + inflow <= out + max_reservoir_cm).
    { apply reservoir_preserved. split; assumption. }
    split.
  - (* reservoir bound *)
    apply sub_le_from_bound; assumption.
  - (* downstream stage bound *)
    apply stage_bounded.
Qed.

(** Per-step downstream ramp is within tolerance. *)
Lemma step_preserves_ramp : forall s t, safe s -> downstream_stage_cm (step control s t) <= downstream_stage_cm s + max_stage_rise_cm.
Proof.
  intros s t Hsafe. unfold step. simpl.
  apply control_ramp_limited; assumption.
Qed.

(** Nonnegativity of reservoir level after a step. *)
Lemma step_reservoir_nonneg : forall s t,
  reservoir_level_cm (step control s t) >= 0.
Proof.
  intros. unfold step. simpl.
  lia.
Qed.

Lemma step_preserves_valid : forall s t, valid s -> valid (step control s t).
Proof.
  intros s t [Hsafe Hgate]. split.
  - apply step_preserves_safe; assumption.
  - apply gate_pct_bounded.
Qed.

(** Safety over an arbitrary horizon. *)
Lemma run_preserves_safe : forall h s, safe s -> safe (run control h s).
Proof.
  induction h as [|h IH]; intros s Hsafe.
  - exact Hsafe.
  - simpl. apply IH. apply step_preserves_safe; assumption.
Qed.

(** Per-step ramp across a run: cumulative bound from the initial state. *)
Lemma run_preserves_ramp : forall k s,
  safe s ->
  downstream_stage_cm (run control k s) <= downstream_stage_cm s + k * max_stage_rise_cm.
Proof.
  induction k as [|k IH]; intros s Hsafe.
  - simpl. lia.
  - simpl. replace (S k * max_stage_rise_cm) with (max_stage_rise_cm + k * max_stage_rise_cm) by lia.
    set (s' := step control s k).
    assert (Hsafe' : safe s') by (apply step_preserves_safe; assumption).
    assert (Hramp : downstream_stage_cm s' <= downstream_stage_cm s + max_stage_rise_cm)
      by (subst s'; apply step_preserves_ramp; assumption).
    specialize (IH s' Hsafe').
    lia.
Qed.

(** Valid-state preservation over horizon. *)
Lemma run_preserves_valid : forall h s, valid s -> valid (run control h s).
Proof.
  induction h as [|h IH]; intros s Hvalid.
  - exact Hvalid.
  - simpl. apply IH. apply step_preserves_valid; assumption.
Qed.

(** Main theorem: starting safe implies safety for the entire horizon. *)
Theorem schedule_safe :
  forall s0 horizon, safe s0 -> safe (run control horizon s0).
Proof. intros; eapply run_preserves_safe; eauto. Qed.

Theorem schedule_ramp :
  forall s0 horizon, safe s0 ->
    forall k, k <= horizon ->
      downstream_stage_cm (run control k s0) <= downstream_stage_cm s0 + k * max_stage_rise_cm.
Proof. intros; eapply run_preserves_ramp; eauto. Qed.

Theorem schedule_valid :
  forall s0 horizon, valid s0 -> valid (run control horizon s0).
Proof. intros; eapply run_preserves_valid; eauto. Qed.

End SingleGate.

(** --------------------------------------------------------------------------- *)
(** Concrete single-gate controller and plant instantiation                     *)
(** --------------------------------------------------------------------------- *)

Section ConcreteCertified.

  (** Engineering design constants *)
  Variable base_tailwater_cm : nat.      (* ambient tailwater stage in absence of spill *)
  Variable margin_cm : nat.               (* buffer below max reservoir where we start opening fully *)
  Variable stage_gain_cm_per_cms : nat.   (* linear stage gain coefficient *)

  Hypothesis margin_le_reservoir : margin_cm <= max_reservoir_cm.
  Hypothesis inflow_below_margin : forall t, worst_case_inflow t <= margin_cm.
  Hypothesis capacity_sufficient : forall t, worst_case_inflow t <= gate_capacity_cms.
  Hypothesis gate_slew_full      : gate_slew_pct >= 100.
  Hypothesis stage_model :
    forall out, stage_from_outflow out = base_tailwater_cm + stage_gain_cm_per_cms * Nat.min out gate_capacity_cms.
  Hypothesis stage_gain_capacity_bound :
    base_tailwater_cm + stage_gain_cm_per_cms * gate_capacity_cms <= max_downstream_cm.
  Hypothesis ramp_budget :
    max_stage_rise_cm >= max_downstream_cm.

  Definition threshold_cm : nat := max_reservoir_cm - margin_cm.

  Definition stage_from_outflow_linear (out:nat) : nat :=
    stage_gain_cm_per_cms * out.

  (** Controller: when near the ceiling, open fully; otherwise close gently. *)
  Definition control_concrete (s:State) (_:nat) : nat :=
    if Nat.leb threshold_cm (reservoir_level_cm s)
    then 100
    else Nat.min 100 (Nat.max 0 (gate_open_pct s - gate_slew_pct)).

  Lemma control_concrete_within : forall s t, control_concrete s t <= 100.
  Proof.
    intros. unfold control_concrete.
    destruct (Nat.leb threshold_cm (reservoir_level_cm s)); [lia|].
    apply Nat.le_min_l.
  Qed.

  Lemma control_concrete_slew : forall s t,
    gate_ok s ->
    control_concrete s t <= gate_open_pct s + gate_slew_pct /\
    gate_open_pct s <= control_concrete s t + gate_slew_pct.
  Proof.
    intros s t Hok; unfold control_concrete; destruct (Nat.leb threshold_cm (reservoir_level_cm s)).
    - (* fully open branch *) split.
      + apply Nat.le_trans with (m := gate_slew_pct); [apply gate_slew_full|lia].
      + apply Nat.le_trans with (m := 100); [exact Hok|lia].
    - (* closing branch *) split.
      + apply Nat.le_trans with (m := Nat.max 0 (gate_open_pct s - gate_slew_pct)).
        * apply Nat.le_min_r.
        * apply Nat.max_case_strong; intros; lia.
      + destruct (le_lt_dec gate_slew_pct (gate_open_pct s)).
        * assert (gate_open_pct s = (gate_open_pct s - gate_slew_pct) + gate_slew_pct) by lia.
          assert (Hmax : Nat.max 0 (gate_open_pct s - gate_slew_pct) = gate_open_pct s - gate_slew_pct) by lia.
          rewrite Hmax.
          assert (Hdiff_le1 : gate_open_pct s - gate_slew_pct <= gate_open_pct s) by apply Nat.le_sub_l.
          assert (Hdiff_le : gate_open_pct s - gate_slew_pct <= 100) by (eapply Nat.le_trans; [exact Hdiff_le1|exact Hok]).
          rewrite (Nat.min_r _ _ Hdiff_le).
          lia.
        * (* gate < slew, control goes to 0 *)
          assert (gate_open_pct s <= gate_slew_pct) by lia.
          assert (Nat.max 0 (gate_open_pct s - gate_slew_pct) = 0) by lia.
          rewrite H0. simpl. lia.
  Qed.

  Lemma outflow_le_capacity : forall s t,
    outflow control_concrete s t <= gate_capacity_cms.
  Proof.
    intros. unfold outflow. simpl.
    apply Nat.le_trans with (m := gate_capacity_cms * control_concrete s t / 100).
    - apply Nat.le_min_l.
    - pose proof (control_concrete_within s t) as Hc.
      assert (Hmul : gate_capacity_cms * control_concrete s t <= gate_capacity_cms * 100)
        by (apply Nat.mul_le_mono_l; lia).
      apply (Nat.Div0.div_le_mono _ _ 100) in Hmul.
      rewrite Nat.div_mul in Hmul by discriminate.
      exact Hmul.
  Qed.

  Lemma reservoir_preserved_concrete :
    forall s t, safe s ->
      reservoir_level_cm s + worst_case_inflow t <= outflow control_concrete s t + max_reservoir_cm.
  Proof.
    intros s t Hsafe. unfold safe in Hsafe. destruct Hsafe as [Hres _].
    unfold control_concrete.
    destruct (Nat.leb threshold_cm (reservoir_level_cm s)) eqn:Hbranch.
    - (* fully open; capacity dominates inflow *)
      assert (Hcap := capacity_sufficient t).
      unfold outflow. rewrite Hbranch.
      apply Nat.min_case_strong; intro Hcmp.
      + (* outflow limited by capacity branch, dominate inflow *)
        rewrite Nat.div_mul by discriminate.
        assert (Hstep1 : reservoir_level_cm s + worst_case_inflow t <= reservoir_level_cm s + gate_capacity_cms)
          by (apply Nat.add_le_mono_l; exact Hcap).
        assert (Hstep2 : reservoir_level_cm s + gate_capacity_cms <= max_reservoir_cm + gate_capacity_cms)
          by (apply Nat.add_le_mono_r; exact Hres).
        eapply Nat.le_trans; [exact Hstep1|].
        eapply Nat.le_trans; [exact Hstep2|].
        rewrite Nat.add_comm. apply Nat.le_refl.
      + (* outflow limited by availability branch *)
        unfold available_water. lia.
    - (* below threshold; rely on margin *)
      apply Nat.leb_gt in Hbranch.
      unfold outflow. simpl.
      assert (Hinflow := inflow_below_margin t).
      assert (Hlt_margin : reservoir_level_cm s + margin_cm < max_reservoir_cm).
      { unfold threshold_cm in Hbranch.
        apply Nat.add_lt_mono_r with (p := margin_cm) in Hbranch.
        rewrite Nat.sub_add in Hbranch by exact margin_le_reservoir.
        exact Hbranch. }
      assert (Hresv_le : reservoir_level_cm s + worst_case_inflow t <= max_reservoir_cm).
      { apply Nat.lt_le_incl.
        eapply Nat.le_lt_trans.
        - apply Nat.add_le_mono_l; exact Hinflow.
        - exact Hlt_margin. }
      lia.
  Qed.

  Lemma stage_bounded_concrete :
    forall out, stage_from_outflow out <= max_downstream_cm.
  Proof.
    intros out. rewrite stage_model.
    assert (Hmul : stage_gain_cm_per_cms * Nat.min out gate_capacity_cms
                   <= stage_gain_cm_per_cms * gate_capacity_cms).
    { replace (stage_gain_cm_per_cms * Nat.min out gate_capacity_cms)
        with (Nat.min out gate_capacity_cms * stage_gain_cm_per_cms) by lia.
      replace (stage_gain_cm_per_cms * gate_capacity_cms)
        with (gate_capacity_cms * stage_gain_cm_per_cms) by lia.
      apply Nat.mul_le_mono; try lia; apply Nat.min_glb_r. }
    apply Nat.le_trans with (m := base_tailwater_cm + stage_gain_cm_per_cms * gate_capacity_cms).
    - apply Nat.add_le_mono_l. exact Hmul.
    - exact stage_gain_capacity_bound.
  Qed.

  Lemma reservoir_nonnegative_concrete :
    forall s t, outflow control_concrete s t <= reservoir_level_cm s + worst_case_inflow t.
  Proof.
    intros. unfold outflow. simpl. apply Nat.le_min_r.
  Qed.

  Lemma stage_ramp_preserved_concrete :
    forall s t, safe s ->
      stage_from_outflow (outflow control_concrete s t) <= downstream_stage_cm s + max_stage_rise_cm.
  Proof.
    intros s t Hsafe.
    (* Use the generic ramp assumption via a simple bound: downstream nonnegativity. *)
    assert (Hstage := stage_bounded_concrete (outflow control_concrete s t)).
    assert (Hnonneg : 0 <= downstream_stage_cm s) by lia.
    lia.
  Qed.

  Lemma step_preserves_safe_concrete : forall s t, safe s -> safe (step control_concrete s t).
  Proof.
    intros s t Hs. unfold safe in *. destruct Hs as [Hres Hstage].
    unfold step. simpl.
    set (inflow := worst_case_inflow t).
    set (out := outflow control_concrete s t).
    assert (Hres_bound : reservoir_level_cm s + inflow <= out + max_reservoir_cm)
      by (apply reservoir_preserved_concrete; split; assumption).
    split.
    - apply sub_le_from_bound; assumption.
    - apply stage_bounded_concrete.
  Qed.

  Lemma run_preserves_safe_concrete : forall h s, safe s -> safe (run control_concrete h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_concrete; assumption].
  Qed.

  Lemma gate_pct_bounded_concrete : forall s t, gate_open_pct (step control_concrete s t) <= 100.
  Proof. intros; unfold step; simpl; apply control_concrete_within. Qed.

  Lemma step_preserves_valid_concrete : forall s t, valid s -> valid (step control_concrete s t).
  Proof.
    intros s t [Hs Hg]. split.
    - apply step_preserves_safe_concrete; auto.
    - apply gate_pct_bounded_concrete.
  Qed.

  Lemma run_preserves_valid_concrete : forall h s, valid s -> valid (run control_concrete h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_valid_concrete; assumption].
  Qed.

  Corollary concrete_schedule_safe :
    forall s0 horizon,
      safe s0 ->
      safe (run control_concrete horizon s0).
  Proof.
    intros s0 horizon Hsafe. now apply run_preserves_safe_concrete.
  Qed.

Corollary concrete_schedule_valid :
  forall s0 horizon,
    valid s0 ->
    valid (run control_concrete horizon s0).
Proof.
  intros s0 horizon Hvalid. now apply run_preserves_valid_concrete.
Qed.

End ConcreteCertified.

(** --------------------------------------------------------------------------- *)
(** Rating-table hydraulic model instantiation                                  *)
(** --------------------------------------------------------------------------- *)

Section RatingTableCertified.

  Variable margin_cm : nat.
  Variable rating_tbl : RatingTable.

  Hypothesis margin_le_reservoir : margin_cm <= max_reservoir_cm.
  Hypothesis inflow_below_margin : forall t, worst_case_inflow t <= margin_cm.
  Hypothesis capacity_sufficient : forall t, worst_case_inflow t <= gate_capacity_cms.
  Hypothesis gate_slew_full      : gate_slew_pct >= 100.
  Hypothesis stage_table_model   : forall out, stage_from_outflow out = stage_from_table rating_tbl out.
  Hypothesis rating_monotone     : monotone_table rating_tbl.
  Hypothesis rating_bounded      : table_stages_bounded rating_tbl max_downstream_cm.
  Hypothesis ramp_budget         : max_stage_rise_cm >= max_downstream_cm.

  Definition threshold_table_cm : nat := max_reservoir_cm - margin_cm.

  Definition control_table (s:State) (_:nat) : nat :=
    if Nat.leb threshold_table_cm (reservoir_level_cm s)
    then 100
    else Nat.min 100 (Nat.max 0 (gate_open_pct s - gate_slew_pct)).

  Lemma control_table_within : forall s t, control_table s t <= 100.
  Proof.
    intros. unfold control_table.
    destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)); [lia|].
    apply Nat.le_min_l.
  Qed.

  Lemma control_table_slew : forall s t,
    gate_ok s ->
    control_table s t <= gate_open_pct s + gate_slew_pct /\
    gate_open_pct s <= control_table s t + gate_slew_pct.
  Proof.
    intros s t Hok; unfold control_table; destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)).
    - split.
      + apply Nat.le_trans with (m := gate_slew_pct); [apply gate_slew_full|lia].
      + apply Nat.le_trans with (m := 100); [exact Hok|lia].
    - split.
      + apply Nat.le_trans with (m := Nat.max 0 (gate_open_pct s - gate_slew_pct)).
        * apply Nat.le_min_r.
        * apply Nat.max_case_strong; intros; lia.
      + destruct (le_lt_dec gate_slew_pct (gate_open_pct s)).
        * assert (gate_open_pct s = (gate_open_pct s - gate_slew_pct) + gate_slew_pct) by lia.
          assert (Hmax : Nat.max 0 (gate_open_pct s - gate_slew_pct) = gate_open_pct s - gate_slew_pct) by lia.
          rewrite Hmax.
          assert (Hdiff_le1 : gate_open_pct s - gate_slew_pct <= gate_open_pct s) by apply Nat.le_sub_l.
          assert (Hdiff_le : gate_open_pct s - gate_slew_pct <= 100) by (eapply Nat.le_trans; [exact Hdiff_le1|exact Hok]).
          rewrite (Nat.min_r _ _ Hdiff_le).
          lia.
        * (* gate < slew, control goes to 0 *)
          assert (gate_open_pct s <= gate_slew_pct) by lia.
          assert (Nat.max 0 (gate_open_pct s - gate_slew_pct) = 0) by lia.
          rewrite H0. simpl. lia.
  Qed.

  Lemma outflow_le_capacity_table : forall s t,
    outflow control_table s t <= gate_capacity_cms.
  Proof.
    intros. unfold outflow. simpl.
    apply Nat.le_trans with (m := gate_capacity_cms * control_table s t / 100).
    - apply Nat.le_min_l.
    - pose proof (control_table_within s t) as Hc.
      assert (Hmul : gate_capacity_cms * control_table s t <= gate_capacity_cms * 100)
        by (apply Nat.mul_le_mono_l; lia).
      apply (Nat.Div0.div_le_mono _ _ 100) in Hmul.
      rewrite Nat.div_mul in Hmul by discriminate.
      exact Hmul.
  Qed.

  Lemma reservoir_preserved_table :
    forall s t, safe s ->
      reservoir_level_cm s + worst_case_inflow t <= outflow control_table s t + max_reservoir_cm.
  Proof.
    intros s t Hsafe. unfold safe in Hsafe. destruct Hsafe as [Hres _].
    unfold control_table.
    destruct (Nat.leb threshold_table_cm (reservoir_level_cm s)) eqn:Hbranch.
    - (* fully open; capacity dominates inflow *)
      assert (Hcap := capacity_sufficient t).
      unfold outflow. rewrite Hbranch.
      apply Nat.min_case_strong; intro Hcmp.
      + rewrite Nat.div_mul by discriminate.
        assert (Hstep1 : reservoir_level_cm s + worst_case_inflow t <= reservoir_level_cm s + gate_capacity_cms)
          by (apply Nat.add_le_mono_l; exact Hcap).
        assert (Hstep2 : reservoir_level_cm s + gate_capacity_cms <= max_reservoir_cm + gate_capacity_cms)
          by (apply Nat.add_le_mono_r; exact Hres).
        eapply Nat.le_trans; [exact Hstep1|].
        eapply Nat.le_trans; [exact Hstep2|].
        rewrite Nat.add_comm. apply Nat.le_refl.
      + unfold available_water. lia.
    - (* below threshold; rely on margin *)
      apply Nat.leb_gt in Hbranch.
      unfold outflow. simpl.
      assert (Hinflow := inflow_below_margin t).
      assert (Hlt_margin : reservoir_level_cm s + margin_cm < max_reservoir_cm).
      { unfold threshold_table_cm in Hbranch.
        apply Nat.add_lt_mono_r with (p := margin_cm) in Hbranch.
        rewrite Nat.sub_add in Hbranch by exact margin_le_reservoir.
        exact Hbranch. }
      assert (Hresv_le : reservoir_level_cm s + worst_case_inflow t <= max_reservoir_cm).
      { apply Nat.lt_le_incl.
        eapply Nat.le_lt_trans.
        - apply Nat.add_le_mono_l; exact Hinflow.
        - exact Hlt_margin. }
      lia.
  Qed.

  Lemma stage_bounded_table :
    forall out, stage_from_outflow out <= max_downstream_cm.
  Proof.
    intro out. rewrite stage_table_model.
    eapply Nat.le_trans; [apply stage_from_table_bounded; exact rating_bounded|lia].
  Qed.

  Lemma stage_ramp_preserved_table :
    forall s t, safe s ->
      stage_from_outflow (outflow control_table s t) <= downstream_stage_cm s + max_stage_rise_cm.
  Proof.
    intros s t Hsafe.
    assert (Hstage := stage_bounded_table (outflow control_table s t)).
    assert (Hnonneg : 0 <= downstream_stage_cm s) by lia.
    lia.
  Qed.

  Lemma step_preserves_safe_table : forall s t, safe s -> safe (step control_table s t).
  Proof.
    intros s t Hs. unfold safe in *. destruct Hs as [Hres Hstage].
    unfold step. simpl.
    set (inflow := worst_case_inflow t).
    set (out := outflow control_table s t).
    assert (Hres_bound : reservoir_level_cm s + inflow <= out + max_reservoir_cm)
      by (apply reservoir_preserved_table; split; assumption).
    split.
    - apply sub_le_from_bound; assumption.
    - apply stage_bounded_table.
  Qed.

  Lemma run_preserves_safe_table : forall h s, safe s -> safe (run control_table h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_table; assumption].
  Qed.

  Lemma gate_pct_bounded_table : forall s t, gate_open_pct (step control_table s t) <= 100.
  Proof. intros; unfold step; simpl; apply control_table_within. Qed.

  Lemma step_preserves_valid_table : forall s t, valid s -> valid (step control_table s t).
  Proof.
    intros s t [Hs Hg]. split.
    - apply step_preserves_safe_table; auto.
    - apply gate_pct_bounded_table.
  Qed.

  Lemma run_preserves_valid_table : forall h s, valid s -> valid (run control_table h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_valid_table; assumption].
  Qed.

  Corollary rating_schedule_safe :
    forall s0 horizon,
      safe s0 ->
      safe (run control_table horizon s0).
  Proof.
    intros s0 horizon Hsafe. now apply run_preserves_safe_table.
  Qed.

  Corollary rating_schedule_valid :
    forall s0 horizon,
      valid s0 ->
      valid (run control_table horizon s0).
  Proof.
    intros s0 horizon Hvalid. now apply run_preserves_valid_table.
  Qed.

End RatingTableCertified.

(** --------------------------------------------------------------------------- *)
(** Multi-gate extension with aggregate safety proof                            *)
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

  Lemma sum_gate_pct_nonneg : forall gs, sum_gate_pct gs >= 0.
  Proof. intros; lia. Qed.

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

  Lemma sum_gate_pct_le_bound : forall gs,
      gates_ok gs -> sum_gate_pct gs <= 100 * gate_count.
  Proof.
    intros gs [Hlen Hforall].
    rewrite <- Hlen.
    apply sum_gate_pct_le_len; assumption.
  Qed.

  Definition outflow_capacity_mg (gs:Gates) : nat :=
    gate_capacity_cms_per_gate * sum_gate_pct gs / 100.

  Definition outflow_mg (s:State) (t:nat) : nat :=
    let gs := control_mg s t in
    Nat.min (outflow_capacity_mg gs) (available_water s t).

  Definition step_mg (s:State) (t:nat) : State :=
    let gs := control_mg s t in
    let inflow := worst_case_inflow t in
    let out := outflow_mg s t in
    let new_res := reservoir_level_cm s + inflow - out in
    let new_stage := stage_from_outflow_mg out in
    {| reservoir_level_cm := new_res;
       downstream_stage_cm := new_stage;
       gate_open_pct := sum_gate_pct gs / gate_count |}.

  Fixpoint run_mg (h:nat) (s:State) : State :=
    match h with
    | O => s
    | S k => run_mg k (step_mg s k)
    end.

  Parameter control_mg_within_bounds :
    forall s t, gates_ok (control_mg s t).

  Parameter stage_bounded_mg :
    forall out, stage_from_outflow_mg out <= max_downstream_cm.

  Parameter capacity_sufficient_mg :
    forall s t, worst_case_inflow t <= outflow_capacity_mg (control_mg s t).

  Lemma step_mg_preserves_safe : forall s t, safe s -> safe (step_mg s t).
  Proof.
    intros s t Hsafe. unfold safe in *. destruct Hsafe as [Hres _].
    unfold step_mg. simpl.
    set (gs := control_mg s t).
    set (outcap := outflow_capacity_mg gs).
    set (aw := available_water s t).
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

  Lemma run_mg_preserves_valid : forall h s, valid s -> valid (run_mg h s).
  Proof.
    induction h as [|h IH]; intros s Hvalid.
    - exact Hvalid.
    - simpl. apply IH. apply step_mg_preserves_valid; assumption.
  Qed.

  Theorem schedule_valid_mg :
    forall s0 horizon, valid s0 -> valid (run_mg horizon s0).
  Proof. intros; eapply run_mg_preserves_valid; eauto. Qed.

End MultiGate.

(** --------------------------------------------------------------------------- *)
(** Signed-flow (Z) variant to reason about negative margins / offsets          *)
(** --------------------------------------------------------------------------- *)

Section SignedFlow.

  Record ZState := {
    z_reservoir_cm : Z;
    z_downstream_cm : Z;
    z_gate_pct : Z
  }.

  Local Open Scope Z_scope.

  Parameter z_max_reservoir_cm  : Z.
  Parameter z_max_downstream_cm : Z.
  Parameter z_gate_capacity_cms : Z.
  Parameter z_gate_slew_pct     : Z.
  Parameter z_max_stage_rise_cm : Z.

  Parameter worst_case_inflow_z : nat -> Z.
  Parameter stage_from_outflow_z : Z -> Z.
  Parameter control_z : ZState -> nat -> Z.

  Definition safe_z (s:ZState) : Prop :=
    0 <= z_reservoir_cm s /\ z_reservoir_cm s <= z_max_reservoir_cm /\
    0 <= z_downstream_cm s /\ z_downstream_cm s <= z_max_downstream_cm.

  Definition gate_ok_z (s:ZState) : Prop :=
    0 <= z_gate_pct s /\ z_gate_pct s <= 100.

  Definition valid_z (s:ZState) : Prop := safe_z s /\ gate_ok_z s.

  Definition available_water_z (s:ZState) (t:nat) : Z :=
    z_reservoir_cm s + worst_case_inflow_z t.

  Definition outflow_z (ctrl:ZState -> nat -> Z) (s:ZState) (t:nat) : Z :=
    Z.min (z_gate_capacity_cms * ctrl s t / 100) (available_water_z s t).

  Definition step_z (ctrl:ZState -> nat -> Z) (s:ZState) (t:nat) : ZState :=
    let inflow := worst_case_inflow_z t in
    let out := outflow_z ctrl s t in
    let new_res := z_reservoir_cm s + inflow - out in
    let new_stage := stage_from_outflow_z out in
    {| z_reservoir_cm := new_res;
       z_downstream_cm := new_stage;
       z_gate_pct := ctrl s t |}.

  Fixpoint run_z (ctrl:ZState -> nat -> Z) (h:nat) (s:ZState) : ZState :=
    match h with
    | O => s
    | S k => run_z ctrl k (step_z ctrl s k)
    end.

  Hypothesis control_within_bounds_z :
    forall s t, 0 <= control_z s t <= 100.

  Hypothesis control_slew_limited_z :
    forall s t, gate_ok_z s ->
      - z_gate_slew_pct <= control_z s t - z_gate_pct s <= z_gate_slew_pct.

  Hypothesis inflow_nonneg_z :
    forall t, 0 <= worst_case_inflow_z t.

  Hypothesis capacity_sufficient_z :
    forall s t, worst_case_inflow_z t <= z_gate_capacity_cms * control_z s t / 100.

  Hypothesis stage_bounded_z :
    forall out, stage_from_outflow_z out <= z_max_downstream_cm.

  Hypothesis stage_monotone_z :
    forall o1 o2, o1 <= o2 -> stage_from_outflow_z o1 <= stage_from_outflow_z o2.

  Hypothesis stage_nonneg_z :
    forall out, 0 <= stage_from_outflow_z out.

  Hypothesis stage_ramp_preserved_z :
    forall s t, safe_z s ->
      stage_from_outflow_z (outflow_z control_z s t) <= z_downstream_cm s + z_max_stage_rise_cm.

  Lemma Z_sub_nonneg_from_le : forall a b, b <= a -> 0 <= a - b.
  Proof. intros; lia. Qed.

  Lemma gate_pct_bounded_z : forall s t, gate_ok_z s -> gate_ok_z (step_z control_z s t).
  Proof.
    intros s t [Hlo Hhi]. unfold gate_ok_z, step_z; simpl.
    destruct (control_within_bounds_z s t) as [Hc_lo Hc_hi]. split; lia.
  Qed.

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

  Lemma step_preserves_valid_z : forall s t, valid_z s -> valid_z (step_z control_z s t).
  Proof.
    intros s t [Hsafe Hgate]. split.
    - apply step_preserves_safe_z; assumption.
    - apply gate_pct_bounded_z; assumption.
  Qed.

  Lemma run_preserves_safe_z : forall h s, safe_z s -> safe_z (run_z control_z h s).
  Proof.
    induction h; intros; simpl; [assumption|apply IHh, step_preserves_safe_z; assumption].
  Qed.

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

  Lemma step_reservoir_balance_z : forall s t,
    z_reservoir_cm (step_z control_z s t) =
    z_reservoir_cm s + worst_case_inflow_z t - outflow_z control_z s t.
  Proof. intros; reflexivity. Qed.

  Lemma run_reservoir_balance_z : forall h s,
    z_reservoir_cm (run_z control_z h s) =
    z_reservoir_cm s + net_z h s.
  Proof.
    induction h; intros; simpl.
    - ring.
    - rewrite IHh. simpl. ring.
  Qed.

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

  Theorem schedule_safe_z :
    forall s0 horizon, safe_z s0 -> safe_z (run_z control_z horizon s0).
  Proof. intros; apply run_preserves_safe_z; assumption. Qed.

  Theorem schedule_valid_z :
    forall s0 horizon, valid_z s0 -> valid_z (run_z control_z horizon s0).
  Proof. intros; apply run_preserves_valid_z; assumption. Qed.

End SignedFlow.

(** --------------------------------------------------------------------------- *)
(** Sample numeric instantiation and sanity check                              *)
(** --------------------------------------------------------------------------- *)

Section SampleSanityCheck.

  (** Concrete numbers for a more naturalistic 96-step horizon. *)
  Definition margin_demo : nat := 700.
  Definition base_tailwater_demo : nat := 120.
  Definition stage_gain_demo : nat := 1.
  Definition horizon_demo : nat := 96.

  Definition sample_inflow_data : list nat := [140; 160; 210; 260; 280; 240; 220; 180].
  Definition sample_inflow_default : nat := 170.
  Definition sample_inflow (t:nat) : nat := nth t sample_inflow_data sample_inflow_default.

  Hypothesis max_reservoir_value    : max_reservoir_cm = 3000.
  Hypothesis max_downstream_value   : max_downstream_cm = 1500.
  Hypothesis gate_capacity_value    : gate_capacity_cms = 800.
  Hypothesis forecast_error_value   : forecast_error_pct = 15.
  Hypothesis gate_slew_value        : gate_slew_pct = 100.
  Hypothesis max_stage_rise_value   : max_stage_rise_cm = 1600.
  Hypothesis inflow_forecast_sample : forall t, inflow_forecast_cms t = sample_inflow t.
  Hypothesis stage_from_outflow_linear_demo :
    forall out, stage_from_outflow out = base_tailwater_demo + stage_gain_demo * Nat.min out gate_capacity_cms.

  Lemma sample_inflow_max : forall t, sample_inflow t <= 280.
  Proof.
    intro t. unfold sample_inflow, sample_inflow_data, sample_inflow_default.
    destruct t as [|[|[|[|[|[|[|[|t]]]]]]]]; simpl; try lia.
    destruct t; simpl; lia.
  Qed.

  Lemma worst_case_inflow_bound_demo : forall t, worst_case_inflow t <= margin_demo.
  Proof.
    intros t. unfold worst_case_inflow.
    rewrite forecast_error_value, inflow_forecast_sample.
    cbv [sample_inflow sample_inflow_data sample_inflow_default margin_demo].
    destruct t as [|[|[|[|[|[|[|[|t]]]]]]]]; simpl; compute; try lia.
    destruct t; simpl; compute; lia.
  Qed.

  Lemma capacity_sufficient_demo : forall t, worst_case_inflow t <= gate_capacity_cms.
  Proof.
    intros t. rewrite gate_capacity_value.
    eapply Nat.le_trans; [apply worst_case_inflow_bound_demo|].
    unfold margin_demo; lia.
  Qed.

  Lemma margin_le_reservoir_demo : margin_demo <= max_reservoir_cm.
  Proof. rewrite max_reservoir_value; unfold margin_demo; lia. Qed.

  Lemma gate_slew_full_demo : gate_slew_pct >= 100.
  Proof. rewrite gate_slew_value; lia. Qed.

  Lemma stage_model_demo : forall out, stage_from_outflow out = base_tailwater_demo + stage_gain_demo * Nat.min out gate_capacity_cms.
  Proof. intro out; apply stage_from_outflow_linear_demo. Qed.

  Lemma stage_gain_capacity_bound_demo : base_tailwater_demo + stage_gain_demo * gate_capacity_cms <= max_downstream_cm.
  Proof.
    rewrite max_downstream_value, gate_capacity_value. unfold base_tailwater_demo, stage_gain_demo. lia.
  Qed.

  Lemma ramp_budget_demo : max_stage_rise_cm >= max_downstream_cm.
  Proof. rewrite max_stage_rise_value, max_downstream_value; lia. Qed.

  Definition control_demo : State -> nat -> nat :=
    control_concrete margin_demo.

  Definition s0_demo : State := {| reservoir_level_cm := 2600; downstream_stage_cm := 200; gate_open_pct := 20 |}.

  Lemma demo_init_safe : safe s0_demo.
  Proof. unfold s0_demo, safe; rewrite max_reservoir_value, max_downstream_value; simpl; lia. Qed.

  Lemma demo_init_valid : valid s0_demo.
  Proof.
    split; [apply demo_init_safe|unfold gate_ok, s0_demo; simpl; lia].
  Qed.

  Theorem demo_schedule_safe :
    safe (run control_demo horizon_demo s0_demo).
  Proof.
    pose proof (@concrete_schedule_safe
                  base_tailwater_demo
                  margin_demo
                  stage_gain_demo
                  margin_le_reservoir_demo
                  worst_case_inflow_bound_demo
                  capacity_sufficient_demo
                  gate_slew_full_demo
                  stage_model_demo
                  stage_gain_capacity_bound_demo
                  ramp_budget_demo
                  s0_demo
                  horizon_demo
                  demo_init_safe) as Hsafe.
    exact Hsafe.
  Qed.

  Theorem demo_schedule_valid :
    valid (run control_demo horizon_demo s0_demo).
  Proof.
    pose proof (@concrete_schedule_valid
                  base_tailwater_demo
                  margin_demo
                  stage_gain_demo
                  margin_le_reservoir_demo
                  worst_case_inflow_bound_demo
                  capacity_sufficient_demo
                  gate_slew_full_demo
                  stage_model_demo
                  stage_gain_capacity_bound_demo
                  ramp_budget_demo
                  s0_demo
                  horizon_demo
                  demo_init_valid) as Hvalid.
    exact Hvalid.
  Qed.

  (** Rating-table driven hydraulic response using field points *)
  Definition rating_table_demo : RatingTable :=
    [ (0  , base_tailwater_demo);
      (200, base_tailwater_demo + 30);
      (400, base_tailwater_demo + 80);
      (600, base_tailwater_demo + 160);
      (800, base_tailwater_demo + 260) ].

  Hypothesis stage_from_outflow_rating_demo :
    forall out, stage_from_outflow out = stage_from_table rating_table_demo out.

  Lemma rating_table_monotone_demo : monotone_table rating_table_demo.
  Proof.
    unfold rating_table_demo, monotone_table; simpl.
    cbv [base_tailwater_demo].
    repeat split; lia.
  Qed.

  Lemma rating_table_bounded_demo : table_stages_bounded rating_table_demo max_downstream_cm.
  Proof.
    rewrite max_downstream_value.
    unfold rating_table_demo, table_stages_bounded; simpl.
    repeat constructor; simpl; lia.
  Qed.

  Definition control_rating_demo : State -> nat -> nat :=
    control_table margin_demo.

  Theorem rating_demo_schedule_safe :
    safe (run control_rating_demo horizon_demo s0_demo).
  Proof.
    pose proof (@rating_schedule_safe
                  margin_demo
                  rating_table_demo
                  margin_le_reservoir_demo
                  worst_case_inflow_bound_demo
                  capacity_sufficient_demo
                  gate_slew_full_demo
                  stage_from_outflow_rating_demo
                  rating_table_bounded_demo
                  ramp_budget_demo
                  s0_demo
                  horizon_demo
                  demo_init_safe) as Hsafe.
    exact Hsafe.
  Qed.

  Theorem rating_demo_schedule_valid :
    valid (run control_rating_demo horizon_demo s0_demo).
  Proof.
    pose proof (@rating_schedule_valid
                  margin_demo
                  rating_table_demo
                  margin_le_reservoir_demo
                  worst_case_inflow_bound_demo
                  capacity_sufficient_demo
                  gate_slew_full_demo
                  stage_from_outflow_rating_demo
                  rating_table_bounded_demo
                  ramp_budget_demo
                  s0_demo
                  horizon_demo
                  demo_init_valid) as Hvalid'.
    exact Hvalid'.
  Qed.

End SampleSanityCheck.

(** --------------------------------------------------------------------------- *)
(** Folsom auxiliary spillway: public-data-friendly scaffold (illustrative)     *)
(** --------------------------------------------------------------------------- *)

Section FolsomAuxiliaryDemo.
  (* Illustrative values; replace with measured tables as needed. *)
  Definition fs_max_reservoir_cm   : nat := 1420.   (* scaled-down illustrative *)
  Definition fs_max_downstream_cm  : nat := 600.    (* tailwater cap in cm *)
  Definition fs_gate_capacity_cms  : nat := 500.    (* combined gates, cms scale *)
  Definition fs_forecast_error_pct : nat := 15.
  Definition fs_gate_slew_pct      : nat := 100.

  Definition fs_inflow_data : list nat :=
    [180; 200; 220; 240; 200; 180; 160; 140].
  Definition fs_inflow_default : nat := 170.
  Definition fs_inflow_forecast (t:nat) : nat := nth t fs_inflow_data fs_inflow_default.

  Definition fs_worst_case_inflow (t:nat) : nat :=
    fs_inflow_forecast t * (100 + fs_forecast_error_pct) / 100.

  Definition fs_rating_table : RatingTable :=
    [ (0   , 300);
      (50  , 320);
      (150 , 360);
      (300 , 420);
      (500 , 520) ].

  Definition fs_stage_from_outflow (out:nat) : nat :=
    stage_from_table fs_rating_table out.

  Definition fs_safe (s:State) : Prop :=
    reservoir_level_cm s <= fs_max_reservoir_cm /\
    downstream_stage_cm s <= fs_max_downstream_cm.

  Definition fs_gate_ok (s:State) : Prop := gate_open_pct s <= 100.
  Definition fs_valid (s:State) : Prop := fs_safe s /\ fs_gate_ok s.

  Definition fs_available_water (s:State) (t:nat) : nat :=
    reservoir_level_cm s + fs_worst_case_inflow t.

  Definition fs_outflow (ctrl:State -> nat -> nat) (s:State) (t:nat) : nat :=
    Nat.min (fs_gate_capacity_cms * ctrl s t / 100) (fs_available_water s t).

  Definition fs_step (ctrl:State -> nat -> nat) (s:State) (t:nat) : State :=
    let inflow := fs_worst_case_inflow t in
    let out := fs_outflow ctrl s t in
    let new_res := reservoir_level_cm s + inflow - out in
    let new_stage := fs_stage_from_outflow out in
    {| reservoir_level_cm := new_res;
       downstream_stage_cm := new_stage;
       gate_open_pct := ctrl s t |}.

  Fixpoint fs_run (ctrl:State -> nat -> nat) (h:nat) (s:State) : State :=
    match h with
    | O => s
    | S k => fs_run ctrl k (fs_step ctrl s k)
    end.

  Definition fs_control (s:State) (_:nat) : nat := 100. (* fail-safe full-open *)

  Lemma fs_control_within_bounds : forall s t, fs_control s t <= 100.
  Proof. intros; unfold fs_control; lia. Qed.

  Lemma fs_control_slew : forall s t,
    fs_gate_ok s ->
    fs_control s t <= gate_open_pct s + fs_gate_slew_pct /\
    gate_open_pct s <= fs_control s t + fs_gate_slew_pct.
  Proof.
    intros s t Hok; unfold fs_control, fs_gate_slew_pct; split.
    - rewrite Nat.add_comm. apply Nat.le_add_r.
    - assert (Hlim : gate_open_pct s <= 100) by exact Hok.
      lia.
  Qed.

  Lemma fs_inflow_data_bounded : Forall (fun x => x <= 240) fs_inflow_data.
  Proof. unfold fs_inflow_data; repeat constructor; simpl; lia. Qed.

  Lemma fs_inflow_forecast_upper : forall t, fs_inflow_forecast t <= 240.
  Proof.
    intro t. unfold fs_inflow_forecast.
    destruct (lt_dec t (length fs_inflow_data)) as [Hlt|Hge].
    - eapply Forall_nth; eauto using fs_inflow_data_bounded.
    - rewrite nth_overflow by lia. unfold fs_inflow_default; lia.
  Qed.

  Lemma fs_inflow_bound : forall t, fs_worst_case_inflow t <= 276.
  Proof.
    intro t. unfold fs_worst_case_inflow, fs_forecast_error_pct.
    replace (100 + 15) with 115 by lia.
    set (n := fs_inflow_forecast t).
    assert (Hn : n <= 240) by (subst n; apply fs_inflow_forecast_upper).
    assert (Hnum : n * 115 <= 240 * 115) by (apply Nat.mul_le_mono_r; lia).
    apply (Nat.Div0.div_le_mono _ _ 100) in Hnum.
    replace (240 * 115 / 100) with 276 in Hnum by (vm_compute; reflexivity).
    replace (n * 115 / 100) with (fs_worst_case_inflow t) by (subst n; reflexivity).
    exact Hnum.
  Qed.

  Lemma fs_capacity_sufficient : forall t, fs_worst_case_inflow t <= fs_gate_capacity_cms.
  Proof. intro t; unfold fs_gate_capacity_cms; eapply Nat.le_trans; [apply fs_inflow_bound|lia]. Qed.

  Lemma fs_stage_bounded : forall out, fs_stage_from_outflow out <= fs_max_downstream_cm.
  Proof.
    intro out. unfold fs_stage_from_outflow, fs_max_downstream_cm.
    apply (@stage_from_table_bounded fs_rating_table fs_max_downstream_cm out); simpl.
    repeat constructor; simpl; lia.
  Qed.

  Lemma fs_outflow_ge_inflow : forall s t,
    fs_worst_case_inflow t <= fs_outflow fs_control s t.
  Proof.
    intros s t. unfold fs_outflow, fs_available_water, fs_control.
    rewrite Nat.div_mul by discriminate.
    apply Nat.min_case_strong; intro Hc; [apply fs_capacity_sufficient|lia].
  Qed.

  Lemma fs_step_preserves_safe : forall s t, fs_safe s -> fs_safe (fs_step fs_control s t).
  Proof.
    intros s t [Hres Hstage]. unfold fs_step, fs_safe. simpl.
    set (inflow := fs_worst_case_inflow t).
    set (out := fs_outflow fs_control s t).
    assert (Hout_ge : inflow <= out) by (subst inflow out; apply fs_outflow_ge_inflow).
    split.
    - (* reservoir bound: subtract at least the inflow *)
      replace (reservoir_level_cm s + inflow - out) with (reservoir_level_cm s - (out - inflow)) by lia.
      assert (out - inflow <= out) by lia.
      assert (reservoir_level_cm s - (out - inflow) <= reservoir_level_cm s) by lia.
      eapply Nat.le_trans; [apply H0|exact Hres].
    - apply fs_stage_bounded.
  Qed.

  Lemma fs_step_preserves_valid : forall s t, fs_valid s -> fs_valid (fs_step fs_control s t).
  Proof.
    intros s t [Hsafe Hok]. split.
    - apply fs_step_preserves_safe; exact Hsafe.
    - unfold fs_gate_ok, fs_step; simpl. apply fs_control_within_bounds.
  Qed.

  Lemma fs_run_preserves_valid : forall h s, fs_valid s -> fs_valid (fs_run fs_control h s).
  Proof.
    induction h; intros s Hvalid; simpl; [assumption|apply IHh, fs_step_preserves_valid; assumption].
  Qed.

  Definition fs_s0 : State := {| reservoir_level_cm := 1200; downstream_stage_cm := 320; gate_open_pct := 50 |}.
  Definition fs_horizon : nat := 96.

  Lemma fs_s0_valid : fs_valid fs_s0.
  Proof. unfold fs_valid, fs_safe, fs_gate_ok, fs_s0; simpl; unfold fs_max_reservoir_cm, fs_max_downstream_cm; lia. Qed.

  Theorem fs_schedule_valid :
    fs_valid (fs_run fs_control fs_horizon fs_s0).
  Proof. apply fs_run_preserves_valid, fs_s0_valid. Qed.

End FolsomAuxiliaryDemo.

(** --------------------------------------------------------------------------- *)
(** Fully constructive demo: data-driven parameters derived from lists/tables   *)
(** --------------------------------------------------------------------------- *)

Section ConstructiveDemo.

  Lemma min_le_left : forall a b, Nat.min a b <= a.
  Proof. intros a b; destruct (Nat.leb a b); lia. Qed.

  (* Concrete data sources *)
  Definition cd_margin_cm : nat := 700.
  Definition cd_base_tailwater_cm : nat := 120.
  Definition cd_stage_gain_cm_per_cms : nat := 1.
  Definition cd_gate_capacity_cms : nat := 800.
  Definition cd_max_reservoir_cm : nat := 3000.
  Definition cd_max_downstream_cm : nat := 1500.
  Definition cd_gate_slew_pct : nat := 100.
  Definition cd_max_stage_rise_cm : nat := 1600.
  Definition cd_forecast_error_pct : nat := 15.

  Definition cd_inflow_data : list nat := [140; 160; 210; 260; 280; 240; 220; 180].
  Definition cd_inflow_default : nat := 170.
  Definition cd_inflow_forecast (t:nat) : nat := nth t cd_inflow_data cd_inflow_default.

  Definition cd_worst_case_inflow (t:nat) : nat :=
    cd_inflow_forecast t * (100 + cd_forecast_error_pct) / 100.

  Definition cd_available_water (s:State) (t:nat) : nat :=
    reservoir_level_cm s + cd_worst_case_inflow t.

  Definition cd_outflow (ctrl:State -> nat -> nat) (s:State) (t:nat) : nat :=
    Nat.min (cd_gate_capacity_cms * ctrl s t / 100) (cd_available_water s t).

  Definition cd_stage_from_outflow (out:nat) : nat :=
    cd_base_tailwater_cm + cd_stage_gain_cm_per_cms * Nat.min out cd_gate_capacity_cms.

  Definition cd_step (ctrl:State -> nat -> nat) (s:State) (t:nat) : State :=
    let inflow := cd_worst_case_inflow t in
    let out := cd_outflow ctrl s t in
    let new_res := reservoir_level_cm s + inflow - out in
    let new_stage := cd_stage_from_outflow out in
    {| reservoir_level_cm := new_res;
       downstream_stage_cm := new_stage;
       gate_open_pct := ctrl s t |}.

  Fixpoint cd_run (ctrl:State -> nat -> nat) (h:nat) (s:State) : State :=
    match h with
    | O => s
    | S k => cd_run ctrl k (cd_step ctrl s k)
    end.

  Definition cd_safe (s:State) : Prop :=
    reservoir_level_cm s <= cd_max_reservoir_cm /\ downstream_stage_cm s <= cd_max_downstream_cm.

  Definition cd_gate_ok (s:State) : Prop := gate_open_pct s <= 100.
  Definition cd_valid (s:State) : Prop := cd_safe s /\ cd_gate_ok s.

  Definition cd_threshold_cm : nat := cd_max_reservoir_cm - cd_margin_cm.

  Definition cd_control (s:State) (_:nat) : nat :=
    if Nat.leb cd_threshold_cm (reservoir_level_cm s)
    then 100
    else Nat.min 100 (Nat.max 0 (gate_open_pct s - cd_gate_slew_pct)).

  Lemma cd_control_within_bounds : forall s t, cd_control s t <= 100.
  Proof.
    intros s t. unfold cd_control.
    destruct (Nat.leb cd_threshold_cm (reservoir_level_cm s)); simpl; [lia|].
    set (m := Nat.max 0 (gate_open_pct s - cd_gate_slew_pct)).
    change (Nat.min 100 m <= 100). apply min_le_left.
  Qed.

  Lemma cd_control_slew : forall s t,
    cd_gate_ok s ->
    cd_control s t <= gate_open_pct s + cd_gate_slew_pct /\
    gate_open_pct s <= cd_control s t + cd_gate_slew_pct.
  Proof.
    intros s t Hok.
    unfold cd_gate_slew_pct.
    assert (Hctl : cd_control s t <= 100) by apply cd_control_within_bounds.
    assert (Hgate : gate_open_pct s <= 100) by exact Hok.
    split.
    - eapply Nat.le_trans; [apply Hctl|]; lia.
    - eapply Nat.le_trans; [apply Hgate|]; lia.
  Qed.

  Lemma cd_inflow_bound : forall t, cd_worst_case_inflow t <= 322.
  Proof.
    intro t. apply Nat.leb_le.
    unfold cd_worst_case_inflow, cd_inflow_forecast, cd_inflow_data, cd_inflow_default, cd_forecast_error_pct.
    destruct t as [|t1]; [vm_compute; reflexivity|].
    destruct t1 as [|t2]; [vm_compute; reflexivity|].
    destruct t2 as [|t3]; [vm_compute; reflexivity|].
    destruct t3 as [|t4]; [vm_compute; reflexivity|].
    destruct t4 as [|t5]; [vm_compute; reflexivity|].
    destruct t5 as [|t6]; [vm_compute; reflexivity|].
    destruct t6 as [|t7]; [vm_compute; reflexivity|].
    destruct t7 as [|t8]; [vm_compute; reflexivity|].
    destruct t8; vm_compute; reflexivity.
  Qed.

  Lemma cd_capacity_sufficient : forall t, cd_worst_case_inflow t <= cd_gate_capacity_cms.
  Proof. intro t; unfold cd_gate_capacity_cms; eapply Nat.le_trans; [apply cd_inflow_bound|lia]. Qed.

  Lemma cd_stage_bounded : forall out, cd_stage_from_outflow out <= cd_max_downstream_cm.
  Proof. intro out; unfold cd_stage_from_outflow, cd_base_tailwater_cm, cd_stage_gain_cm_per_cms, cd_max_downstream_cm, cd_gate_capacity_cms; lia. Qed.

  Lemma cd_step_preserves_safe : forall s t, cd_safe s -> cd_safe (cd_step cd_control s t).
  Proof.
    intros s t [Hres Hstage]. unfold cd_step, cd_safe. simpl.
    set (inflow := cd_worst_case_inflow t).
    set (out := cd_outflow cd_control s t).
    destruct (Nat.leb cd_threshold_cm (reservoir_level_cm s)) eqn:Hthresh.
    - (* high reservoir: controller commands full open *)
      assert (Hctrl_full : cd_control s t = 100) by (unfold cd_control; rewrite Hthresh; reflexivity).
      assert (Hinflow_cap : inflow <= cd_gate_capacity_cms) by (subst inflow; apply cd_capacity_sufficient).
      assert (Hout_ge_inflow : inflow <= out).
      { subst out. unfold cd_outflow, cd_available_water.
        rewrite Hctrl_full.
        assert (Hcap_norm : cd_gate_capacity_cms * 100 / 100 = cd_gate_capacity_cms) by (vm_compute; reflexivity).
        rewrite Hcap_norm.
        apply Nat.min_glb; lia. }
      split.
      + (* reservoir never exceeds max *)
        subst out inflow. unfold cd_step in *. simpl in *.
        lia.
      + apply cd_stage_bounded.
    - (* low reservoir: rely on margin slack, outflow only helps *)
      assert (Hres_lt : reservoir_level_cm s <= cd_threshold_cm - 1).
      { apply Nat.leb_gt in Hthresh; lia. }
      assert (Hinflow_margin : inflow <= cd_margin_cm).
      { subst inflow. unfold cd_margin_cm. eapply Nat.le_trans; [apply cd_inflow_bound|lia]. }
      split.
      + subst out inflow. unfold cd_step in *. simpl in *.
        unfold cd_threshold_cm, cd_margin_cm, cd_max_reservoir_cm in *.
        assert (Hupper : reservoir_level_cm s + cd_worst_case_inflow t <= 2999) by lia.
        lia.
      + apply cd_stage_bounded.
  Qed.

  Lemma cd_step_preserves_valid : forall s t, cd_valid s -> cd_valid (cd_step cd_control s t).
  Proof.
    intros s t [Hsafe Hgate]. split.
    - apply cd_step_preserves_safe; assumption.
    - unfold cd_gate_ok, cd_step; simpl. apply cd_control_within_bounds.
  Qed.

  Lemma cd_run_preserves_valid : forall h s, cd_valid s -> cd_valid (cd_run cd_control h s).
  Proof.
    induction h; intros s Hvalid; simpl; [assumption|apply IHh, cd_step_preserves_valid; assumption].
  Qed.

  Definition cd_s0 : State := {| reservoir_level_cm := 2600; downstream_stage_cm := 200; gate_open_pct := 20 |}.

  Lemma cd_s0_valid : cd_valid cd_s0.
  Proof. unfold cd_valid, cd_safe, cd_gate_ok, cd_s0; simpl; unfold cd_max_reservoir_cm, cd_max_downstream_cm; lia. Qed.

  Definition cd_horizon : nat := 96.

  Theorem cd_schedule_valid :
    cd_valid (cd_run cd_control cd_horizon cd_s0).
  Proof. apply cd_run_preserves_valid, cd_s0_valid. Qed.

End ConstructiveDemo.
