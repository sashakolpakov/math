import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.Ampleness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Group Hom Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness.Construction

noncomputable section

/-! Ampleness is equivalent to ampleness of its pullback under a finite,
flat, surjective homomorphism over an infinite field with connected
target. The kernel is the actual fibre product over the identity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] [Infinite K]
  {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [PreconnectedSpace B.left]
  (q : A ⟶ B) [IsMonHom q]
  [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

theorem finiteFlat_groupHom_isAmple_of_pullback
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (hL : (L.pullback q.left).IsAmple) : L.IsAmple := by
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject q).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite q
  apply IsogenyQuotient.Field.Ampleness.Construction.group_quotient_isAmple_of_pullback (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q) q _ L hL
  intro T x
  constructor
  · intro hx
    let z := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv q T).symm ⟨x, hx⟩
    have hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q = x := pullback.lift_fst _ _ _
    exact ⟨z, hz, fun z' hz' => (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion q)).mp
      (hz'.trans hz.symm)⟩
  · rintro ⟨z, hz, _⟩
    rw [← hz, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]

theorem finiteFlat_groupHom_isAmple_iff (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) :
    L.IsAmple ↔ (L.pullback q.left).IsAmple := by
  constructor
  · intro hL
    exact hL.pullback_of_isAffineHom q.left
  · exact finiteFlat_groupHom_isAmple_of_pullback q L

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness.Construction
