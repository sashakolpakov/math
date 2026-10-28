import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Cube Proper Global Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperGlobalSections.Construction.CubeCech

noncomputable section

/-! Global regular functions on the proper integral schemes used in the degree argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def globalConstants {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Over an algebraically closed field, every global regular function on
a universally closed integral scheme is constant. -/
theorem globalConstants_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (globalConstants f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

def properIntegralGlobalSectionsEquiv
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f] :
    k ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (globalConstants f) (globalConstants_bijective f)

/-- Every morphism from a proper integral scheme to an affine scheme
factors through the algebraically closed base field. -/
theorem factors_through_base_of_proper_integral
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f]
    [IsAffine Y] (g : X ⟶ Y) : ∃ a : Spec (.of k) ⟶ Y, f ≫ a = g := by
  let e := (properIntegralGlobalSectionsEquiv f).toCommRingCatIso
  have hf : X.toSpecΓ ≫ Spec.map e.hom = f := by
    change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    simp
  refine ⟨Spec.map (g.appTop ≫ e.inv) ≫ Y.isoSpec.inv, ?_⟩
  rw [← hf, Spec.map_comp]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, e.inv_hom_id]
  have hid : Spec.map (𝟙 (CommRingCat.of ↑Γ(X, ⊤))) = 𝟙 (Spec Γ(X, ⊤)) :=
    Spec.map_id _
  rw [hid, Category.id_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProperGlobalSections.Construction.CubeCech
