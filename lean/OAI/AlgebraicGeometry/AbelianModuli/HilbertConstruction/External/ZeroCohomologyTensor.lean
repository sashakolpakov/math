import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalSectionCechLinearity

/-! # Zero Cohomology Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.ZeroCohomologyTensor

noncomputable section

/-! The global degree-zero cohomology of an external tensor bundle is the
tensor product of the two degree-zero cohomology modules, with the actual
coefficient action. No higher-degree acyclicity is needed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def coefficientPushforwardZeroCohomologyIso
    {X Y : Scheme.{u}} {R : Type u} [CommRing R]
    (b : X ⟶ Y) (c : R →+* Γ(Y, ⊤)) (M : X.Modules) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj ((Scheme.Modules.pushforward b).obj M) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (b.appTop.hom.comp c) 0).obj M := by
  have htop : b ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ := by ext x; simp
  exact (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv c
      ((Scheme.Modules.pushforward b).obj M)).toModuleIso ≪≫
    (Coefficient.PushforwardModuleComparison.coefficientPushforwardModuleComponent b c M ⊤).toModuleIso ≪≫
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (b.appTop.hom.comp c) M).mapIso (eqToIso (congrArg op htop)) ≪≫
    (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (b.appTop.hom.comp c) M).toModuleIso.symm

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

def fieldExternalZeroCohomologyModuleIso (hU : iSup U = ⊤) :
    (tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf)).obj
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor g.appTop.hom 0).obj N.sheaf) ≅
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (b.appTop.hom.comp g.appTop.hom) 0).obj
      (((L.pullback a).tensor (N.pullback b)).sheaf) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let T := tensorRight B
  let : Module.Flat Γ(Spec (.of k), ⊤) B := inferInstance
  let : PreservesFiniteColimits T :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight B)
  let C := Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U
  let E := ((L.pullback a).tensor (N.pullback b)).sheaf
  let eN := (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    g.appTop.hom N.sheaf).toModuleIso ≪≫
      CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso g.appTop.hom N.sheaf U hU
  exact T.mapIso eN ≪≫ ((C.sc 0).mapHomologyIso T).symm ≪≫
    HomologicalComplex.homologyMapIso
      (HilbertConstruction.Field.ExternalSectionCechLinearity.fieldExternalSectionsCechModuleIso H L N V hV haV heV U haU heU) 0 ≪≫
    (CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso g.appTop.hom ((Scheme.Modules.pushforward b).obj E) U hU).symm ≪≫
    (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
      g.appTop.hom ((Scheme.Modules.pushforward b).obj E)).toModuleIso.symm ≪≫
    coefficientPushforwardZeroCohomologyIso b g.appTop.hom E

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.ZeroCohomologyTensor
