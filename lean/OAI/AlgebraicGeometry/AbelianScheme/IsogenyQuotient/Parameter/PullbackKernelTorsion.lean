import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackTrivialLineTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperGroupParameterFunctions
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Pullback Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackKernelTorsion.Construction

noncomputable section

/-! Over every affine parameter, line classes in the actual isogeny
pullback kernel are killed by an exponent of the original kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

universe u
variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

omit [IsMonHom f] [Surjective f.left] in
theorem parameterPullbackKernel_projection_appTop_isIso
    (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f))
      ((Over.pullback Q.hom).obj A)).left.appTop := by
  let f' := (Over.pullback Q.hom).map f
  have hf : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have hflat : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have hfp : LocallyOfFinitePresentation f'.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').hom := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f' ⟨hf, hflat, hfp⟩).1
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f').hom
  exact ProperGroupParameterFunctions.Construction.properGroup_parameter_product_appTop_isIso A Q (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')

theorem parameterPullbackTrivialClass_torsion
    (Q : Over (Spec (.of k))) [IsAffine Q.left]
    (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass ((Over.pullback Q.hom).obj B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left c =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left)
    (n : ℕ) (hn : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    c ^ n = 1 := by
  let f' := (Over.pullback Q.hom).map f
  have : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have : Surjective f'.left := MorphismProperty.overPullbackMap (P := @Surjective) Q.hom _ inferInstance
  have : IsMonHom f' := inferInstance
  let : GrpObj (Picard.Homomorphisms.Kernel.Construction.kernelScheme f') := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup f'
  have := parameterPullbackKernel_projection_appTop_isIso f Q
  apply PullbackTrivialLineTorsion.Construction.pullbackTrivialClass_torsion f' c hc n
  intro U x
  apply (CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.baseChangeKernelPointMulEquiv f Q.hom U).injective
  rw [map_pow, hn, map_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackKernelTorsion.Construction
