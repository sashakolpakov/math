import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ConnectedEtaleLifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Etale Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EtaleCancellation.Construction

noncomputable section

/-! Connectedness cancels finite etale maps between actual abelian
schemes, and proves the group law for a lift that preserves the origin. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

variable {k : Type} [Field k] {g : ℕ}

theorem abelian_tensor_preconnected (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
    PreconnectedSpace (A.scheme ⊗ A.scheme).left := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  exact inferInstanceAs (PreconnectedSpace (pullback A.scheme.hom A.scheme.hom : Scheme))

theorem abelian_hom_ext_after_finite_etale
    (A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : B.scheme ⟶ C.scheme) [IsFinite f.left] [Etale f.left]
    (a b : A.scheme ⟶ B.scheme) [IsMonHom a] [IsMonHom b]
    (h : a ≫ f = b ≫ f) : a = b := by
  have : PreconnectedSpace A.scheme.left :=
    ConnectedEtaleLifts.Construction.preconnected_of_geometricallyConnected_over_field A.scheme.hom
  have : Nonempty (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Nonempty (Spec (.of k)))
  apply Over.OverMorphism.ext
  apply ConnectedEtaleLifts.Construction.finite_etale_lifts_equal_of_connected f.left a.left b.left
    (congrArg Over.Hom.left h) η[A.scheme].left
  exact congrArg Over.Hom.left ((IsMonHom.one_hom a).trans (IsMonHom.one_hom b).symm)

theorem abelian_map_isMonHom_of_finite_etale_comp
    (A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : B.scheme ⟶ C.scheme) [IsMonHom f] [IsFinite f.left] [Etale f.left]
    (a : A.scheme ⟶ B.scheme) [IsMonHom (a ≫ f)]
    (hzero : η[A.scheme] ≫ a = η[B.scheme]) : IsMonHom a where
  one_hom := hzero
  mul_hom := by
    have : PreconnectedSpace (A.scheme ⊗ A.scheme).left := abelian_tensor_preconnected A
    have : Nonempty (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Nonempty (Spec (.of k)))
    have hcomp : (μ[A.scheme] ≫ a) ≫ f = ((a ⊗ₘ a) ≫ μ[B.scheme]) ≫ f := by
      rw [Category.assoc, IsMonHom.mul_hom (a ≫ f), Category.assoc,
        IsMonHom.mul_hom f, ← Category.assoc, tensorHom_comp_tensorHom]
    let z : 𝟙_ (Over (Spec (.of k))) ⟶ A.scheme ⊗ A.scheme := lift η[A.scheme] η[A.scheme]
    have hz : z ≫ (μ[A.scheme] ≫ a) = z ≫ ((a ⊗ₘ a) ≫ μ[B.scheme]) := by
      have hμz : z ≫ μ[A.scheme] = η[A.scheme] := by
        rw [MonObj.mul_eq_mul, MonObj.comp_mul]
        simp [z, MonObj.one_eq_one]
      have hza : z ≫ (a ⊗ₘ a) = lift η[B.scheme] η[B.scheme] := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [z, hzero]
      calc
        _ = η[A.scheme] ≫ a := by rw [← Category.assoc, hμz]
        _ = η[B.scheme] := hzero
        _ = lift η[B.scheme] η[B.scheme] ≫ μ[B.scheme] := by
          simp [MonObj.mul_eq_mul, MonObj.comp_mul, MonObj.one_eq_one]
        _ = _ := by rw [← Category.assoc, hza]
    apply Over.OverMorphism.ext
    exact ConnectedEtaleLifts.Construction.finite_etale_lifts_equal_of_connected f.left (μ[A.scheme] ≫ a).left
      ((a ⊗ₘ a) ≫ μ[B.scheme]).left (congrArg Over.Hom.left hcomp) z.left
      (congrArg Over.Hom.left hz)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EtaleCancellation.Construction
