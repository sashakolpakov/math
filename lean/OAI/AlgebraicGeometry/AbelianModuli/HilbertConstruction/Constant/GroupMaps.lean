import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Group Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps

noncomputable section

/-! Pointwise descriptions of maps between constant group functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology

universe u v

variable {S : Scheme.{u}} {G H : Type v} [Group G] [Group H]

/-- The group-valued functor of locally constant sections of a constant group. -/
def constantGroupFunctor (S : Scheme.{u}) (G : Type v) [Group G] :
    (Over S)ᵒᵖ ⥤ GrpCat.{max u v} where
  obj T := GrpCat.of (LocallyConstant T.unop.left G)
  map f := GrpCat.ofHom (LocallyConstant.comapMonoidHom ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id T := by
    ext x t
    rfl
  map_comp f h := by
    ext x t
    rfl

/-- Evaluation on constant base sections gives a homomorphism of the label groups. -/
def constantGroupMapAt (α : constantGroupFunctor S G ⟶ constantGroupFunctor S H)
    (s : S) : G →* H where
  toFun g := LocallyConstant.toFun
    (α.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S g)) s
  map_one' := congrArg (fun c : LocallyConstant S H => c s)
    ((α.app (.op (Over.mk (𝟙 S)))).hom.map_one)
  map_mul' g h := congrArg (fun c : LocallyConstant S H => c s)
    ((α.app (.op (Over.mk (𝟙 S)))).hom.map_mul
      (LocallyConstant.const S g) (LocallyConstant.const S h))

/-- Naturality forces a map of constant group functors to act pointwise on labels. -/
theorem constantGroupMap_apply (α : constantGroupFunctor S G ⟶ constantGroupFunctor S H)
    (T : Over S) (c : LocallyConstant T.left G) (x : T.left) :
    LocallyConstant.toFun (α.app (.op T) c) x = constantGroupMapAt α (T.hom x) (c x) := by
  let U : T.left.Opens := ⟨{y | c y = c x}, c.isLocallyConstant.isOpen_fiber (c x)⟩
  let V : Over S := Over.mk (U.ι ≫ T.hom)
  let j : V ⟶ T := Over.homMk U.ι rfl
  let b : V ⟶ Over.mk (𝟙 S) := Over.homMk (U.ι ≫ T.hom) (Category.comp_id _)
  let y : U.toScheme := ⟨x, rfl⟩
  have hj : c.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const V.left (c x) := by
    apply LocallyConstant.ext
    intro z
    exact z.property
  have wj := congrArg (fun d : LocallyConstant V.left H => d y)
    (ConcreteCategory.congr_hom (α.naturality j.op) c)
  change LocallyConstant.toFun (α.app (.op V) (c.comap ⟨j.left, j.left.continuous⟩)) y =
    LocallyConstant.toFun (α.app (.op T) c) x at wj
  rw [hj] at wj
  have wb := congrArg (fun d : LocallyConstant V.left H => d y)
    (ConcreteCategory.congr_hom (α.naturality b.op) (LocallyConstant.const S (c x)))
  change LocallyConstant.toFun (α.app (.op V) (LocallyConstant.const V.left (c x))) y =
    constantGroupMapAt α (T.hom x) (c x) at wb
  exact wj.symm.trans wb

/-- The pointwise label homomorphisms determine a map of constant group functors. -/
theorem constantGroupMap_ext
    {α β : constantGroupFunctor S G ⟶ constantGroupFunctor S H}
    (h : ∀ s, constantGroupMapAt α s = constantGroupMapAt β s) : α = β := by
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  apply LocallyConstant.ext
  intro x
  exact (constantGroupMap_apply α T.unop c x).trans
    ((congrArg (fun a : G →* H => a (LocallyConstant.toFun c x)) (h (T.unop.hom x))).trans
      (constantGroupMap_apply β T.unop c x).symm)

/-- For a finite label group, the pointwise homomorphism varies locally constantly. -/
def constantGroupMapLabels [Finite G]
    (α : constantGroupFunctor S G ⟶ constantGroupFunctor S H) :
    LocallyConstant S (G →* H) where
  toFun := constantGroupMapAt α
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    have h : ∀ᶠ t in 𝓝 s, ∀ g : G,
        constantGroupMapAt α t g = constantGroupMapAt α s g :=
      Filter.eventually_all.mpr (fun g =>
        (α.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S g) :
          LocallyConstant S H).isLocallyConstant.eventually_eq s)
    exact h.mono (fun _ ht => MonoidHom.ext ht)

/-- Apply a locally constant family of label homomorphisms to a section. -/
def applyConstantGroupLabels (a : LocallyConstant S (G →* H))
    (T : Over S) (c : LocallyConstant T.left G) : LocallyConstant T.left H where
  toFun x := a (T.hom x) (c x)
  isLocallyConstant :=
    (a.isLocallyConstant.comp_continuous T.hom.continuous).comp₂ c.isLocallyConstant
      (fun f g => f g)

/-- Locally constant label homomorphisms act naturally on all test schemes. -/
def constantGroupMapOfLabels (a : LocallyConstant S (G →* H)) :
    constantGroupFunctor S G ⟶ constantGroupFunctor S H where
  app T := GrpCat.ofHom {
    toFun := applyConstantGroupLabels a T.unop
    map_one' := by
      apply LocallyConstant.ext
      intro x
      exact map_one (a (T.unop.hom x))
    map_mul' c d := by
      apply LocallyConstant.ext
      intro x
      exact map_mul (a (T.unop.hom x)) (c x) (d x) }
  naturality {T U} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro (c : LocallyConstant T.unop.left G)
    apply LocallyConstant.ext
    intro x
    change a (U.unop.hom x) (LocallyConstant.toFun c (f.unop.left x)) =
      a (T.unop.hom (f.unop.left x)) (LocallyConstant.toFun c (f.unop.left x))
    rw [← Scheme.Hom.comp_apply, f.unop.w]

/-- Maps of finite constant group functors are precisely locally constant families
of homomorphisms between their label groups. -/
def constantGroupMapEquiv [Finite G] :
    (constantGroupFunctor S G ⟶ constantGroupFunctor S H) ≃ LocallyConstant S (G →* H) where
  toFun := constantGroupMapLabels
  invFun := constantGroupMapOfLabels
  left_inv α := by
    apply constantGroupMap_ext
    intro s
    apply MonoidHom.ext
    intro g
    rfl
  right_inv a := by
    apply LocallyConstant.ext
    intro s
    apply MonoidHom.ext
    intro g
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps
