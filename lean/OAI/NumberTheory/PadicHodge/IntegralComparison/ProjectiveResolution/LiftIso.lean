import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomNaturality

/-! # Lift Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.LiftIso

noncomputable section

/-! Any lift of the identity between projective resolutions induces an
isomorphism after applying an additive contravariant functor and taking
cohomology. The statement concerns the given lift, not a chosen one. -/

open _root_.CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false

universe u v w z

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive] {M : C}
  (P Q : ProjectiveResolution M) (a : P.complex ⟶ Q.complex)
  (ha : a ≫ Q.π = P.π)

include ha in
theorem homology_isIso (n : ℕ) :
    IsIso (HomNaturality.map F a n) := by
  have h : Homotopy a (ProjectiveResolution.lift (𝟙 M) P Q) :=
    ProjectiveResolution.liftHomotopy (𝟙 M) _ _ (by simpa using ha)
      (ProjectiveResolution.lift_commutes (𝟙 M) P Q)
  rw [HomNaturality.map_eq_of_homotopy F h n,
    ← HomNaturality.iso_hom F Q P n]
  infer_instance

include ha in
theorem quasiIso : QuasiIso ((HomNaturality.functor F).map a.op) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact homology_isIso F P Q a ha n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.LiftIso
