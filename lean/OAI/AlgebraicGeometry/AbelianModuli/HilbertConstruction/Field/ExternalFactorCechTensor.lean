import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafTermCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.Isomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstDifferentialInjectivity
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # External Factor Cech Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFactorCechTensor

noncomputable section

/-! The cohomology-factor Cech complex of an external line bundle is the right tensor of the parameter's coefficient Cech complex with proper-factor cohomology. The tuple isomorphisms use actual factor restrictions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

theorem moduleTensorRight_map_eq_scalarMap
    {R : Type u} [CommRing R] {A B : ModuleCat.{u} R} (f : A ⟶ B) (V : ModuleCat.{u} R) :
    (tensorRight V).map f = (Module.TensorHomologyNaturality.ModuleTensorFunctor.scalarMap f.hom).app V := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a v
  rfl

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

def fieldExternalFactorCechTensorIso (n : ℕ) :
    ((tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf) ⋙
      Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)).mapHomologicalComplex (.up ℕ)).obj
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex g.appTop.hom N.sheaf U) ≅
    (cechComplexFunctor (fun i => b ⁻¹ᵁ U i)).obj
      (Cech.SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)) (n + 1)) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let W (p : ℕ) (i : Fin (p + 1) → κ) : Y.Opens := ∏ᶜ fun j => U (i j)
  have hW (p : ℕ) (i : Fin (p + 1) → κ) : IsAffineOpen (W p i) := Affine.CechIntersections.affine_cechIntersection U haU p i
  let eW (p : ℕ) (i : Fin (p + 1) → κ) :
      (Scheme.Modules.pullback (W p i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (W p i).toScheme :=
    N.frameRestrict (leOfHom (Pi.π (fun j : Fin (p + 1) => U (i j)) 0)) (heU (i 0)).some
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf
  let T := tensorRight B ⋙ Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf ⋙ T
  let E := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf)
  let G := (Opens.map b.base).op ⋙ Cech.SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf E (n + 1)
  let e (p : ℕ) (i : Fin (p + 1) → κ) : F.obj (op (W p i)) ≅ G.obj (op (W p i)) :=
    Intrinsic.ExternalFactorCohomology.nativeExternalFactorCohomologyIso H L N (W p i) (hW p i) (eW p i) V hV haV heV n
  have he : ∀ (p : ℕ) (j : Fin (p + 2)) (i : Fin (p + 2) → κ),
      F.map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ i).op ≫
          (e (p + 1) i).hom =
        (e p (i ∘ (SimplexCategory.δ j).toOrderHom.toFun)).hom ≫
          G.map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ i).op := by
    intro p j i
    let i' := i ∘ (SimplexCategory.δ j).toOrderHom.toFun
    let hle : W (p + 1) i ≤ W p i' := Cech.SheafCofaces.IntrinsicCech.cechTupleLE U p j i
    have h := Intrinsic.ExternalFactorCohomologyNaturality.nativeExternalFactorCohomologyIso_restrict H L N hle
      (hW p i') (hW (p + 1) i) (eW p i') (eW (p + 1) i) V hV haV heV n
    change (Module.ProductForget.moduleForget Γ(Spec (.of k), ⊤)).map
        ((tensorRight B).map ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).map
          (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ i).op)) ≫
      (e (p + 1) i).hom = _
    rw [moduleTensorRight_map_eq_scalarMap]
    exact h
  exact HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso T (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf) U ≪≫
    CechTuple.Isomorphism.cechComplexIsoOfTupleIsos U e he ≪≫
      (Additive.CechPushforward.additiveCechPushforwardComplexIso b (Cech.SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf E (n + 1)) U).symm

include H hV haV heV haU heU in
theorem fieldExternal_cechCohomology_firstDifferential_injective
    (hU : iSup U = ⊤) (hN : Subsingleton Γ(N.sheaf, ⊤)) (n : ℕ) :
    Function.Injective (CategoryTheory.Sheaf.H.map
      (Cech.SheafDifferential.IntrinsicCech.cechDifferential
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))
        (fun i => b ⁻¹ᵁ U i) 0) (n + 1)) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  apply Cech.SheafTermCohomology.IntrinsicCech.cechCohomology_firstDifferential_injective
  apply CechTuple.Isomorphism.additiveCochain_firstDifferential_injective_of_iso
    (fieldExternalFactorCechTensorIso H L N V hV haV heV U haU heU n)
  exact Cech.FirstDifferentialInjectivity.coefficientCech_tensorRight_firstDifferential_injective g.appTop.hom N.sheaf U hU hN
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFactorCechTensor
