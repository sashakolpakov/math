import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafExactness
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Sheaf Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels.Construction

noncomputable section

/-!
# CartierDuality: detecting actual fppf-sheaf kernels on every test scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

namespace CommutativeSheaves

/-- The concrete kernel subgroup gives a kernel fork in commutative groups. -/
def kernelCone {G Q : CommGrpCat.{u}} (q : G ⟶ Q) : KernelFork q :=
  KernelFork.ofι (Z := CommGrpCat.of q.hom.ker) (CommGrpCat.ofHom q.hom.ker.subtype) (by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨x, hx⟩
    exact hx)

/-- The concrete kernel subgroup has the categorical universal property. -/
def kernelIsLimit {G Q : CommGrpCat.{u}} (q : G ⟶ Q) : IsLimit (kernelCone q) :=
  Fork.IsLimit.mk _
    (fun s => CommGrpCat.ofHom (s.ι.hom.codRestrict _ (fun x =>
      ConcreteCategory.congr_hom s.condition x)))
    (fun _ => rfl)
    (fun _ _ h => by
      apply CommGrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      exact Subtype.ext (ConcreteCategory.congr_hom h x))

/-- A monomorphism whose image is the concrete kernel gives the same
kernel, as a multiplicative equivalence. -/
def kernelPointsEquiv {H G Q : CommGrpCat.{u}} (i : H ⟶ G) (q : G ⟶ Q)
    (w : i ≫ q = 0) [Mono i] (h : ∀ x : G, q x = 1 → ∃ y : H, i y = x) : H ≃* q.hom.ker :=
  MulEquiv.ofBijective
    (i.hom.codRestrict q.hom.ker (fun x => ConcreteCategory.congr_hom w x))
    ⟨fun x y he => (CommGrpCat.mono_iff_injective i).mp inferInstance (congrArg Subtype.val he),
      fun x => by
        obtain ⟨y, hy⟩ := h x.val x.property
        exact ⟨y, Subtype.ext hy⟩⟩

/-- A pointwise kernel description of commutative groups is its
categorical kernel description. -/
def kernelIsLimitOfPoints {H G Q : CommGrpCat.{u}} (i : H ⟶ G) (q : G ⟶ Q)
    (w : i ≫ q = 0) [Mono i] (h : ∀ x : G, q x = 1 → ∃ y : H, i y = x) :
    IsLimit (KernelFork.ofι i w) :=
  IsLimit.ofIsoLimit (kernelIsLimit q)
    (Fork.ext (kernelPointsEquiv i q w h).toCommGrpIso rfl).symm

end CommutativeSheaves

namespace Schemes

/-- A monomorphism of commutative fppf sheaves is the kernel of a map
when its sections are the kernel on every test scheme. -/
def sheafKernelIsLimitOfPoints {S : Scheme.{u}} {H G Q : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (i : H ⟶ G) (q : G ⟶ Q) (w : i ≫ q = 0) [Mono i]
    (h : ∀ (T : Over S) (x : G.obj.obj (Opposite.op T)),
      q.hom.app (Opposite.op T) x = 1 →
        ∃ y : H.obj.obj (Opposite.op T), i.hom.app (Opposite.op T) y = x) :
    IsLimit (KernelFork.ofι i w) := by
  apply isLimitOfReflects (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro T
  let V := sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} ⋙
    (evaluation (Over S)ᵒᵖ CommGrpCat.{u + 1}).obj T
  have hw : V.map i ≫ V.map q = 0 := by rw [← V.map_comp, w, V.map_zero]
  have hi : Mono (V.map i) := inferInstance
  have hk := CommutativeSheaves.kernelIsLimitOfPoints (V.map i) (V.map q) hw (h T.unop)
  exact (isLimitMapConeForkEquiv' V w).symm hk

end Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels.Construction
