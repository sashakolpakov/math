import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Homomorphisms Polarization Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction

noncomputable section

/-! Convert the original fixed-dimension abelian scheme and its
polarization to Homomorphisms's proved native API. The actual Poincare bundle,
map, positivity witnesses and group law are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

def e57AbelianOfBundled {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    Picard.Homomorphisms.AbelianSchemes.Construction.AbelianScheme S where
  toOver := A.scheme
  group := A.group
  commutative := A.commutative
  proper := A.proper
  smooth := inferInstance
  connected := A.connected

variable {S T : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem e57PoincarePullback_ofBundled (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : T ⟶ S) :
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.poincarePullbackOverMap f).left =
      (D.poincarePullbackOverMap f).left := by
  rfl

def e57PolarizationBiextensionIso (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (((Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme).left)
      ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.pullback f).poincare).sheaf ≅
        (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p f).sheaf :=
  (Scheme.Modules.pullbackComp
    (((Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme).left)
    (((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.poincarePullbackOverMap f).left)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg
      (fun z => (((Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme).left) ≫ z)
      ((e57PoincarePullback_ofBundled D f).trans
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D f).symm))).app D.poincare.sheaf

theorem e57PositiveOnGeometricFiber_ofBundled (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (k : Type u) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ S) (hp : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p k s) :
    Picard.Homomorphisms.Polarizations.Construction.PositiveOnGeometricFiber (e57AbelianOfBundled A)
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup p k s := by
  obtain ⟨L, hL, hzero, ⟨hformula⟩⟩ := hp
  refine ⟨L, hL, hzero, ⟨?_⟩⟩
  exact AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (e57PolarizationBiextensionIso D p s) (Iso.refl _)) (Iso.refl _) ≪≫ hformula

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}

def e57PolarizationOfBundled (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
    (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) : Picard.Homomorphisms.Polarizations.Construction.Polarization (e57AbelianOfBundled A) where
  representation := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  map := p.isogeny.hom
  preservesGroup := by
    have h := p.isogeny.preservesGroup
    change @IsMonHom _ _ _ _ _ A.group.toMonObj
      (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup
        (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)).toMonObj p.isogeny.hom
    rw [Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_ofBundled, Picard.Homomorphisms.DualGroupComparison.Construction.dualPicardGroup_eq_given]
    exact h
  finite := p.isogeny.finite
  flat := p.isogeny.flat
  surjective := p.isogeny.surjective
  positive l _ _ s := e57PositiveOnGeometricFiber_ofBundled D p.isogeny.hom l s (p.positive l s)

theorem e57PolarizationOfBundled_map (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
    (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) : (e57PolarizationOfBundled D p).map = p.isogeny.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction
