import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.OneFirst

/-! # Acyclic Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.AcyclicShift

noncomputable section

/-! Native Tor dimension shifting only needs the indicated Tor groups
of the middle term to vanish. This applies to exact tensor images of
presentations even when those images are not projective. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

variable (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)

def shiftIso (n : ℕ)
    (h₁ : IsZero (((Tor (ModuleCat R) (n + 2)).obj S.X₂).obj N))
    (h₂ : IsZero (((Tor (ModuleCat R) (n + 1)).obj S.X₂).obj N)) :
    (((Tor (ModuleCat R) (n + 2)).obj S.X₃).obj N) ≅
      (((Tor (ModuleCat R) (n + 1)).obj S.X₁).obj N) := by
  let : Mono (ExactSequence.connecting R N S hS (n + 1)) :=
    (ExactSequence.exact_before_connecting R N S hS (n + 1)).mono_g
      (h₁.eq_of_src _ _)
  let : Epi (ExactSequence.connecting R N S hS (n + 1)) :=
    (ExactSequence.exact_after_connecting R N S hS (n + 1)).epi_f
      (h₂.eq_of_tgt _ _)
  let := isIso_of_mono_of_epi (ExactSequence.connecting R N S hS (n + 1))
  exact asIso (ExactSequence.connecting R N S hS (n + 1))

def kernelIso (h₁ : IsZero (((Tor (ModuleCat R) 1).obj S.X₂).obj N)) :
    (((Tor (ModuleCat R) 1).obj S.X₃).obj N) ≅
      ModuleCat.of R ((tensorRight N).map S.f).hom.ker := by
  let δ := ExactSequence.connecting R N S hS 0
  let : Mono δ := (ExactSequence.exact_before_connecting R N S hS 0).mono_g
    (h₁.eq_zero_of_src _)
  let e₁ := Flat.torZeroIso R S.X₁ N
  let e₂ := Flat.torZeroIso R S.X₂ N
  let g := (tensorRight N).map S.f
  let : HasKernel g := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit g⟩
  have hw : (δ ≫ e₁.hom) ≫ g = 0 := by
    rw [Category.assoc, ← OneFirst.zero_naturality R N S.f, ← Category.assoc,
      ExactSequence.connecting_comp, zero_comp]
  let T := ShortComplex.mk (δ ≫ e₁.hom) g hw
  let e : ShortComplex.mk δ (((Tor (ModuleCat R) 0).map S.f).app N)
      (ExactSequence.connecting_comp R N S hS 0) ≅ T :=
    ShortComplex.isoMk (Iso.refl _) e₁ e₂ (by simp [T])
      (OneFirst.zero_naturality R N S.f).symm
  have hT : T.Exact := ShortComplex.exact_of_iso e
    (ExactSequence.exact_after_connecting R N S hS 0)
  let : Mono T.f := inferInstanceAs (Mono (δ ≫ e₁.hom))
  exact (limit.isoLimitCone ⟨_, hT.fIsKernel⟩).symm ≪≫ ModuleCat.kernelIsoKer g

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.AcyclicShift
