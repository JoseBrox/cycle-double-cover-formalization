import RequestProject.Flows

open scoped BigOperators

set_option autoImplicit false

namespace CycleDoubleCover

/-- **Finite-dimensional duality criterion.** A vector lies in the range of a linear map iff it
is annihilated by every functional that annihilates the range. -/
theorem mem_range_iff_annihilated_by_dual {K U W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (L : U →ₗ[K] W) (d : W) :
    d ∈ LinearMap.range L ↔
      ∀ φ : Module.Dual K W, (∀ x, φ (L x) = 0) → φ d = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) d]
  constructor
  · intro h φ hφ
    exact h φ (Submodule.mem_dualAnnihilator φ |>.mpr
      (by rintro w ⟨x, rfl⟩; exact hφ x))
  · intro h φ hφ
    refine h φ (fun x => ?_)
    exact (Submodule.mem_dualAnnihilator φ).1 hφ (L x) ⟨x, rfl⟩

namespace CDCDual

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Coordinate functional of a dual vector on `E → Γ`, at edge `e`. -/
noncomputable def coordFunctional (φ : Module.Dual F2 (E → Gamma)) (e : E) : GammaDual :=
  φ.comp (LinearMap.single F2 (fun _ : E => Gamma) e)

@[simp] lemma coordFunctional_apply (φ : Module.Dual F2 (E → Gamma)) (e : E) (x : Gamma) :
    coordFunctional φ e x = φ (Pi.single e x) := rfl

/-- Finite-sum expansion of a functional on `E → Γ` via its coordinate functionals. -/
lemma dual_expansion (φ : Module.Dual F2 (E → Gamma)) (w : E → Gamma) :
    φ w = ∑ e, coordFunctional φ e (w e) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  rfl

end CDCDual

end CycleDoubleCover
