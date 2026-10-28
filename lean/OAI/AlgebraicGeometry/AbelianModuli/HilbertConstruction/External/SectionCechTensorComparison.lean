import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.RingTheory.Flat.CategoryTheory
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalAllCechTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FactorDegreeZero

/-! # Section Cech Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionCechTensorComparison

noncomputable section

/-! A finite affine frame cover compares the sections of an external tensor
bundle with the tensor product of the sections of its factors. This file
constructs the additive comparison; coefficient linearity is separate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

def fieldExternalSectionsCechTensorIso :
    ((tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf) ⋙
      HilbertConstruction.Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)).mapHomologicalComplex (.up ℕ)).obj
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U) ≅
    (cechComplexFunctor (fun i => b ⁻¹ᵁ U i)).obj
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)).obj :=
  HilbertConstruction.Field.ExternalAllCechTensor.fieldExternalFactorAllCechTensorIso H L N V hV haV heV U haU heU 0 ≪≫
    (cechComplexFunctor (fun i => b ⁻¹ᵁ U i)).mapIso
      (Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyPresheafIso
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)))

def fieldExternalZeroCohomologyAddIso (hU : iSup U = ⊤) :
    (HilbertConstruction.Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)).obj
      ((tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf)).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor g.appTop.hom 0).obj N.sheaf)) ≅
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).obj
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let T := tensorRight B ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)
  letI : Module.Flat Γ(Spec (.of k), ⊤) B := inferInstance
  letI : PreservesFiniteLimits T := inferInstance
  letI : PreservesFiniteColimits (tensorRight B) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight B)
  letI : PreservesFiniteColimits (HilbertConstruction.Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)) := inferInstance
  letI : PreservesFiniteColimits T := comp_preservesFiniteColimits _ _
  let C := Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U
  let E := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let eN := (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    g.appTop.hom N.sheaf).toModuleIso ≪≫
      CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso g.appTop.hom N.sheaf U hU
  exact T.mapIso eN ≪≫ ((C.sc 0).mapHomologyIso T).symm ≪≫
    HomologicalComplex.homologyMapIso
      (fieldExternalSectionsCechTensorIso H L N V hV haV heV U haU heU) 0 ≪≫
    (IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso (fun i => b ⁻¹ᵁ U i) E
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top b U hU)).symm ≪≫
    (CategoryTheory.Sheaf.H.equiv₀ E
      (isTerminalTop : IsTerminal (⊤ : Opens P.carrier))).symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionCechTensorComparison
