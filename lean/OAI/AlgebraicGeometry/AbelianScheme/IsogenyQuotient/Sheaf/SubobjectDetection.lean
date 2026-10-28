import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.KernelSections
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Subobject Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.SubobjectDetection.Construction

noncomputable section

/-! The actual sections on every test scheme detect inclusion and
equality of commutative fppf-sheaf subobjects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (J K : Subobject F)

theorem sheafSubobject_le_of_sections
    (h : ∀ T : Over S, KernelSections.Construction.sheafSubobjectSections T J ≤ KernelSections.Construction.sheafSubobjectSections T K) : J ≤ K := by
  have hi (T : (Over S)ᵒᵖ) : Function.Injective (K.arrow.hom.app T) :=
    (CommGrpCat.mono_iff_injective _).mp inferInstance
  have hex (T : (Over S)ᵒᵖ) (x : (J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S).obj.obj T) :
      ∃ y, K.arrow.hom.app T y = J.arrow.hom.app T x := h T.unop ⟨x, rfl⟩
  let lift (T : (Over S)ᵒᵖ) (x : (J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S).obj.obj T) := (hex T x).choose
  have hl (T : (Over S)ᵒᵖ) (x : (J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S).obj.obj T) :
      K.arrow.hom.app T (lift T x) = J.arrow.hom.app T x := (hex T x).choose_spec
  let m : (J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) ⟶ (K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) := {
    hom.app T := CommGrpCat.ofHom {
      toFun := lift T
      map_one' := by apply hi T; rw [hl, map_one, map_one]
      map_mul' x y := by apply hi T; rw [hl, map_mul, map_mul, hl, hl] }
    hom.naturality := by
      intro T U f
      apply CommGrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      apply hi U
      change K.arrow.hom.app U (lift U ((J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S).obj.map f x)) =
        K.arrow.hom.app U ((K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S).obj.map f (lift T x))
      rw [hl]
      have hJ := ConcreteCategory.congr_hom (J.arrow.hom.naturality f) x
      have hK := ConcreteCategory.congr_hom (K.arrow.hom.naturality f) (lift T x)
      exact hJ.trans ((congrArg ((F.obj.map f)) (hl T x)).symm.trans hK.symm) }
  apply Subobject.le_of_comm m
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  exact hl T

theorem sheafSubobject_eq_of_sections
    (h : ∀ T : Over S, KernelSections.Construction.sheafSubobjectSections T J = KernelSections.Construction.sheafSubobjectSections T K) : J = K :=
  le_antisymm (sheafSubobject_le_of_sections J K (fun T => (h T).le))
    (sheafSubobject_le_of_sections K J (fun T => (h T).ge))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.SubobjectDetection.Construction
