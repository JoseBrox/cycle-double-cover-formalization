import RequestProject.Flows

open scoped BigOperators
open scoped Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace CycleDoubleCover

/-- The "nonzero bit" of a dual vector. -/
noncomputable def nzBit (η : GammaDual) : F2 := if η = 0 then 0 else 1

/-
In a one-dimensional vector space over `𝔽₂`, any two nonzero vectors are equal.
-/
lemma eq_of_ne_zero_of_finrank_one {W : Type*} [AddCommGroup W] [Module F2 W]
    (h : Module.finrank F2 W = 1) {a b : W} (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  have h_line := finrank_eq_one_iff'.mp h;
  obtain ⟨ v, hv, hv' ⟩ := h_line; obtain ⟨ c, rfl ⟩ := hv' a; obtain ⟨ d, rfl ⟩ := hv' b; rcases Fin.exists_fin_two.mp ⟨ c, rfl ⟩ with ( rfl | rfl ) <;> rcases Fin.exists_fin_two.mp ⟨ d, rfl ⟩ with ( rfl | rfl ) <;> simp_all +decide ;

/-
Over `𝔽₂`, two distinct nonzero vectors form a linearly independent pair.
-/
lemma linIndep_pair_of_ne (x y : Gamma) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent F2 ![x, y] := by
  refine' linearIndependent_fin2.mpr _;
  simp_all +decide [ funext_iff, Fin.forall_fin_two ];
  intro a; by_cases ha : a = 0 <;> simp_all +decide [ eq_comm ] ;
  fin_cases a <;> simp_all +decide

/-
The dual annihilator of the span of an independent pair in `Γ` (dimension 3) is a line.
-/
lemma finrank_dualAnnihilator_span_pair (x y : Gamma) (hxy : LinearIndependent F2 ![x, y]) :
    Module.finrank F2 (Submodule.span F2 {x, y}).dualAnnihilator = 1 := by
  have h_finrank : Module.finrank F2 (Submodule.span F2 {x, y}) = 2 := by
    convert finrank_span_eq_card hxy;
    · aesop;
    · aesop;
    · congr;
      · aesop;
      · infer_instance;
  have h_dualAnnihilator : ∀ (W : Submodule F2 Gamma), Module.finrank F2 (Submodule.dualAnnihilator W) = Module.finrank F2 Gamma - Module.finrank F2 W := by
    intro W; have := Subspace.finrank_add_finrank_dualAnnihilator_eq W; simp_all +decide [ Nat.sub_add_cancel ] ;
    lia;
  rw [ h_dualAnnihilator, h_finrank ] ; norm_num [ Module.finrank_pi ] ;

/-
Parity bookkeeping: three dual vectors summing to zero and lying in a line contribute an
even number of nonzero terms.
-/
lemma nzBit_sum_eq_zero_of_line {W : Submodule F2 Gamma}
    (hdim : Module.finrank F2 W.dualAnnihilator = 1)
    (ηa ηb ηc : GammaDual)
    (ha : ηa ∈ W.dualAnnihilator) (hb : ηb ∈ W.dualAnnihilator) (hc : ηc ∈ W.dualAnnihilator)
    (hsum : ηa + ηb + ηc = 0) :
    nzBit ηa + nzBit ηb + nzBit ηc = 0 := by
  by_cases ha0 : ηa = 0 <;> by_cases hb0 : ηb = 0 <;> by_cases hc0 : ηc = 0 <;> simp_all +decide only [nzBit];
  · aesop;
  · aesop;
  · aesop;
  · -- Since ηa, ηb, and ηc are all nonzero and lie in a one-dimensional subspace, they must be equal.
    have h_eq : ηa = ηb ∧ ηb = ηc := by
      have h_eq : ∀ (η : GammaDual), η ∈ W.dualAnnihilator → ∀ (ν : GammaDual), ν ∈ W.dualAnnihilator → η ≠ 0 → ν ≠ 0 → η = ν := by
        intros η hη ν hν hη0 hν0;
        have := eq_of_ne_zero_of_finrank_one hdim ( show ( ⟨ η, hη ⟩ : W.dualAnnihilator ) ≠ 0 from by simpa [ Subtype.ext_iff ] using hη0 ) ( show ( ⟨ ν, hν ⟩ : W.dualAnnihilator ) ≠ 0 from by simpa [ Subtype.ext_iff ] using hν0 ) ; aesop;
      exact ⟨ h_eq ηa ha ηb hb ha0 hb0, h_eq ηb hb ηc hc hb0 hc0 ⟩;
    simp_all +decide [ ← two_smul F2, CharTwo.two_eq_zero ]

set_option maxHeartbeats 1000000 in
/-- **The local dual-parity lemma (equations (7)–(9)).**
For `x, y, z : Γ` with `z = x + y`, all nonzero, and dual vectors `ηa, ηb, ηc` summing to `0`
and annihilating `x, y, z` respectively, the value `ηb x` equals the parity of the number of
nonzero members of `{ηa, ηb, ηc}`. -/
lemma local_dual_parity (x y z : Gamma) (ηa ηb ηc : GammaDual)
    (hz : z = x + y) (hx : x ≠ 0) (hy : y ≠ 0) (hznz : z ≠ 0)
    (hsum : ηa + ηb + ηc = 0)
    (hax : ηa x = 0) (hby : ηb y = 0) (hcz : ηc z = 0) :
    ηb x = nzBit ηa + nzBit ηb + nzBit ηc := by
  by_cases hx : ηb x = 0;
  · have h_mem : ηa ∈ (Submodule.span F2 {x, y}).dualAnnihilator ∧ ηb ∈ (Submodule.span F2 {x, y}).dualAnnihilator ∧ ηc ∈ (Submodule.span F2 {x, y}).dualAnnihilator := by
      simp_all +decide [ Submodule.mem_dualAnnihilator, Submodule.mem_span_pair ];
      simp_all +decide [ ← eq_sub_iff_add_eq', funext_iff ];
      refine' ⟨ _, _, _ ⟩;
      · intro w a b hw; rw [ show w = a • x + b • y by ext i; simp [ hw i ] ] ; simp +decide [ *, map_add, map_smul ] ;
      · intro w a b hb; rw [ show w = a • x + b • y by ext i; simpa [ mul_comm ] using by have := hb i; rw [ eq_sub_iff_add_eq ] at this; simp_all +decide [ mul_comm ] ] ; simp +decide [ *, map_add, map_smul ] ;
      · intro w a b hw; rw [ show w = a • x + b • y by ext i; simp [ hw i ] ] ; simp +decide [ *, map_add, map_smul ] ;
    have h_finrank : Module.finrank F2 (Submodule.span F2 {x, y}).dualAnnihilator = 1 := by
      apply finrank_dualAnnihilator_span_pair;
      apply linIndep_pair_of_ne x y ‹_› ‹_›;
      intro h; simp_all +decide [ CharTwo.add_self_eq_zero ] ;
    have := nzBit_sum_eq_zero_of_line h_finrank ηa ηb ηc h_mem.1 h_mem.2.1 h_mem.2.2 hsum; aesop;
  · -- Since ηb x ≠ 0, we have nzBit ηa = 1, nzBit ηb = 1, and nzBit ηc = 1.
    have h_nzBits : nzBit ηa = 1 ∧ nzBit ηb = 1 ∧ nzBit ηc = 1 := by
      unfold nzBit; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
    cases Fin.exists_fin_two.mp ⟨ ηb x, rfl ⟩ <;> simp_all +decide

end CycleDoubleCover
