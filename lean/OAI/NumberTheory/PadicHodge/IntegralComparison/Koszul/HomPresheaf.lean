import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrderedProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor

/-! # Hom Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheaf

noncomputable section

/-! The actual Hom Koszul cochain complex with varying module
coefficients. Its restriction maps and differentials are literal
postcomposition and precomposition. -/
open _root_.CategoryTheory Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {C : Type u} [Category C]
  (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V] [Module R V]
  (P : Cᵒᵖ ⥤ ModuleCat.{u} R)

def homPresheaf (p : ℕ) : Cᵒᵖ ⥤ ModuleCat.{u} R where
  obj a := ModuleCat.of R ((⋀[R]^p V) →ₗ[R] P.obj a)
  map f := ModuleCat.ofHom
    { toFun := fun φ => (P.map f).hom.comp φ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_id a := by
    apply ModuleCat.hom_ext
    ext φ x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext φ x
    simp

variable (l : Module.Dual R V)

def differential (p : ℕ) : homPresheaf R V P p ⟶ homPresheaf R V P (p + 1) where
  app a := ModuleCat.ofHom
    { toFun := fun φ => φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l p)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality _ _ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

theorem differential_square (p : ℕ) : differential R V P l p ≫ differential R V P l (p + 1) = 0 := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change (show (⋀[R]^p V) →ₗ[R] P.obj a from φ) ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l p)
    ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l (p + 1)) x)) = 0
  have h := LinearMap.congr_fun (Exterior.KoszulComplex.contraction_square R V l p) x
  change (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l p)
    ((AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l (p + 1)) x) = 0 at h
  rw [h, map_zero]

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  CochainComplex.of (homPresheaf R V P) (differential R V P l) (differential_square R V P l)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheaf
