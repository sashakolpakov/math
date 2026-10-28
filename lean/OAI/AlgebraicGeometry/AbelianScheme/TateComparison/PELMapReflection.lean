import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints

/-! # PEL Map Reflection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELMapReflection

noncomputable section

/-! Faithful base change reflects the actual PEL polarization and action
equations. The dual map is identified by Poincare universality and its
proved compatibility with base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {S T : Scheme} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S}
  (b : T ⟶ S) (f : P.abelian.scheme ⟶ Q.abelian.scheme) [IsMonHom f]
  (e : PELIsogenies.PELIsogeny (P.pullback b) (Q.pullback b) n)
  (hf : (Over.pullback b).map f = e.isogeny.hom)

include hf in
theorem pel_native_dual_pullback :
    (Over.pullback b).map (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f P.dual Q.dual) = e.dualHom := by
  have hd : e.dualHom = FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap b f)
      (P.dual.pullback b) (Q.dual.pullback b) := by
    apply FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dualHom ⊗ₘ 𝟙 _).left _ =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 _ ⊗ₘ (Over.pullback b).map f).left _
    rw [hf]
    exact e.poincare.symm
  exact (FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange b f P.dual Q.dual).trans hd.symm

include hf in
theorem pel_native_polarization_of_pullback [(Over.pullback b).Faithful] :
    f ≫ Q.polarizationMap.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f P.dual Q.dual = P.polarizationMap.hom ^ n := by
  apply (Over.pullback b).map_injective
  simp only [Functor.map_comp]
  rw [pel_native_dual_pullback b f e hf, hf, PELBaseChange.pullback_map_pow]
  exact e.polarization

omit [IsMonHom f] in
include hf in
theorem pel_action_of_pullback [(Over.pullback b).Faithful] (r : R) :
    End.endSchemeMap P.abelian.scheme (P.action r) ≫ f =
      f ≫ End.endSchemeMap Q.abelian.scheme (Q.action r) := by
  apply (Over.pullback b).map_injective
  simp only [Functor.map_comp]
  rw [hf, ← P.pullback_action_schemeMap b r, ← Q.pullback_action_schemeMap b r]
  exact e.equivariant r

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELMapReflection
