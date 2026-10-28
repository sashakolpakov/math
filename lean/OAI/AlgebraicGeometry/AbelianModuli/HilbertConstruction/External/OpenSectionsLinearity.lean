import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalZeroCohomologyScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalAllCohomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFactorCechTensor

/-! # Open Sections Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsLinearity

noncomputable section

/-! The affine-parameter external section comparison is linear for the
original coefficient action. The scalar identity comes from the native
pairing, rather than an action transported along an additive isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rTensor_smul_identity_apply
    {R : Type u} [CommRing R] (A B : Type u)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (r : R) (x : A ⊗[R] B) : ((r • (LinearMap.id : A →ₗ[R] A)).rTensor B) x = r • x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.smul_apply,
      LinearMap.id_apply, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

variable {S X Y P : Scheme.{u}} [IsAffine S] [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable (U : Y.Opens) (haU : IsAffineOpen U)
variable (eU : (Scheme.Modules.pullback U.ι).obj N.sheaf ≅ Line.Bundles.structureModule U.toScheme)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : iSup V = ⊤)
variable (ha : ∀ i, IsAffineOpen (V i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))]

def externalOpenSectionsModuleIso :
    (tensorRight ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf)).obj
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)) ≅
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f.appTop.hom)
      (((L.pullback a).tensor (N.pullback b)).sheaf)).obj (op (b ⁻¹ᵁ U)) := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
  let B := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf
  let E := ((L.pullback a).tensor (N.pullback b)).sheaf
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf E
  let e₀ := Intrinsic.ExternalFactorAllCohomology.nativeExternalFactorAllCohomologyIso H L N U haU eU V hV ha he 0
  let e₁ := Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso F (b ⁻¹ᵁ U)
  let φ := e₀ ≪≫ e₁
  let C := (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f.appTop.hom) E).obj (op (b ⁻¹ᵁ U))
  let eLin : A ⊗[Γ(S, ⊤)] B ≃ₗ[Γ(S, ⊤)] C :=
    { toAddEquiv := φ.addCommGroupIsoToAddEquiv
      map_smul' := by
        intro r x
        let s := UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom
          (Global.ModuleScalars.globalModuleScalar E ((a.appTop.hom.comp f.appTop.hom) r))
        let t := Open.FactorSheafNaturality.IntrinsicCech.cechOpenFactorMap s (b ⁻¹ᵁ U)
        have hs : e₀.hom (r • x) =
            (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map t (e₀.hom x) := by
          have h := ConcreteCategory.congr_hom
            (Intrinsic.ExternalZeroCohomologyScalars.nativeExternalFactorZeroCohomologyIso_scalar H L N U haU eU V hV ha he r) x
          change e₀.hom (((r • (LinearMap.id : A →ₗ[Γ(S, ⊤)] A)).rTensor B) x) = _ at h
          simp only [rTensor_smul_identity_apply, ConcreteCategory.comp_apply] at h
          exact h
        have ht : e₁.hom
            ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).map t (e₀.hom x)) =
              s.hom.app (op (b ⁻¹ᵁ U)) (e₁.hom (e₀.hom x)) :=
          ConcreteCategory.congr_hom
            (Open.FactorSheafNaturality.IntrinsicCech.cechFactorZeroCohomologyIso_sheaf_naturality s (b ⁻¹ᵁ U)) (e₀.hom x)
        change e₁.hom (e₀.hom (r • x)) = r • (show C from e₁.hom (e₀.hom x))
        rw [hs, ht]
        rfl }
  exact eLin.toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.OpenSectionsLinearity
