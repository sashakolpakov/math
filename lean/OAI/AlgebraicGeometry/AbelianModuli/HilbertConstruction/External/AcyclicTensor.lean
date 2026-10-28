import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionCechTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicFactorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalCechFactorVanishing

/-! # Acyclic Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicTensor

noncomputable section

/-! External tensor products of two line bundles without positive
cohomology also have no positive cohomology. -/
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

include H hV haV heV haU heU in
theorem fieldExternal_positiveCohomology_vanish (hU : iSup U = ⊤)
    (hL : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf (q + 1)))
    (hN : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N.sheaf (q + 1))) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (((L.pullback a).tensor (N.pullback b)).sheaf) (q + 1)) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  have : N.sheaf.IsQuasicoherent := N.isQuasicoherent
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let T := tensorRight B ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)
  let : Module.Flat Γ(Spec (.of k), ⊤) B := inferInstance
  let : PreservesFiniteColimits (tensorRight B) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesFiniteColimits T := comp_preservesFiniteColimits _ _
  let C := Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U
  let E := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  have hzN : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor g.appTop.hom (q + 1)).obj N.sheaf) := by
    let : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor g.appTop.hom (q + 1)).obj N.sheaf) := hN q
    exact ModuleCat.isZero_of_subsingleton _
  have hzC : IsZero (C.homology (q + 1)) :=
    (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso g.appTop.hom N.sheaf U hU haU q).isZero_iff.mpr hzN
  have hzT : IsZero (((T.mapHomologicalComplex (.up ℕ)).obj C).homology (q + 1)) :=
    ((C.sc (q + 1)).mapHomologyIso T).symm.isZero_iff.mp (T.map_isZero hzC)
  have hFactors : ∀ p r (i : Fin (p + 1) → κ),
      Subsingleton (CategoryTheory.Sheaf.H (IntrinsicCech.SheafTerms.cechTermFactor E (fun i => b ⁻¹ᵁ U i) p i) (r + 1)) := by
    intro p r i
    exact HilbertConstruction.Field.ExternalCechFactorVanishing.fieldExternal_cechTermFactor_cohomology_vanish H L N V hV haV heV U haU heU p i (r + 1) (hL r)
  let eC := SectionCechTensorComparison.fieldExternalSectionsCechTensorIso H L N V hV haV heV U haU heU
  let eH := Cech.AcyclicFactorComparison.IntrinsicCech.cechCohomologyIsoOfAcyclicFactors E (fun i => b ⁻¹ᵁ U i)
    (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top b U hU) hFactors (q + 1)
  exact AddCommGrpCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyMapIso eC (q + 1) ≪≫ eH).isZero_iff.mp hzT)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicTensor
