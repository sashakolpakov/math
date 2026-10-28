import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps

/-! # Constant Sections On -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

noncomputable section

/-! Extend sections indexed by a group to locally constant sections on every
test scheme. The extension uses the actual disjoint union of open fibers;
its group laws and naturality are proved without a torsion trivialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {I : Type} {H : Over S}

abbrev baseTest (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)

def toBase (T : Over S) : T ⟶ baseTest S :=
  Over.homMk T.hom (Category.comp_id _)

def component (S : Scheme.{0}) (i : I) : baseTest S ⟶ HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) i) (HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)

def sectionsMap (h : I → (baseTest S ⟶ H)) : HilbertConstruction.ConstantScheme.Iff.constantScheme S I ⟶ H :=
  Over.homMk (Sigma.desc (fun i => (h i).left)) (by
    change (Sigma.desc (fun i => (h i).left)) ≫ H.hom = Sigma.desc (fun _ : I => 𝟙 S)
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact (h i).w)

@[simp]
theorem component_sectionsMap (h : I → (baseTest S ⟶ H)) (i : I) :
    component S i ≫ sectionsMap h = h i := by
  apply Over.OverMorphism.ext
  exact Sigma.ι_comp_desc _ _

def extend (h : I → (baseTest S ⟶ H)) (T : Over S)
    (c : LocallyConstant T.left I) : T ⟶ H :=
  (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm c ≫ sectionsMap h

theorem extend_natural (h : I → (baseTest S ⟶ H)) {T U : Over S}
    (j : U ⟶ T) (c : LocallyConstant T.left I) :
    extend h U (c.comap ⟨j.left, j.left.continuous⟩) = j ≫ extend h T c := by
  have hw : (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I U).symm
      (c.comap ⟨j.left, j.left.continuous⟩) =
      j ≫ (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm c := by
    apply (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I U).injective
    rw [Equiv.apply_symm_apply]
    exact ((HilbertConstruction.Constant.BaseChange.constantSetRepresentable S I).homEquiv_comp j
      ((HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm c)).trans
        (congrArg (fun d : LocallyConstant T.left I =>
          d.comap ⟨j.left, j.left.continuous⟩)
          ((HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).apply_symm_apply c)) |>.symm
  exact (congrArg (fun f => f ≫ sectionsMap h) hw).trans (Category.assoc _ _ _)

theorem extend_const (h : I → (baseTest S ⟶ H)) (T : Over S) (i : I) :
    extend h T (LocallyConstant.const T.left i) = toBase T ≫ h i := by
  have hw : (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).symm
      (LocallyConstant.const T.left i) = toBase T ≫ component S i := by
    apply (HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).injective
    rw [Equiv.apply_symm_apply]
    apply LocallyConstant.ext
    intro x
    exact (HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (T.hom x)).symm
  rw [extend, hw, Category.assoc, component_sectionsMap]

def fiberTest (T : Over S) (c : LocallyConstant T.left I) (i : I) : Over S :=
  Over.mk ((HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι ≫ T.hom)

def fiberInclusion (T : Over S) (c : LocallyConstant T.left I) (i : I) :
    fiberTest T c i ⟶ T := Over.homMk (HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι rfl

theorem hom_ext_on_fibers (T : Over S) (c : LocallyConstant T.left I)
    {f g : T ⟶ H} (h : ∀ i, fiberInclusion T c i ≫ f = fiberInclusion T c i ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso c).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc, HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc]
  exact congrArg Over.Hom.left (h i)

variable {G : Type} [Group G] [GrpObj H]

/-- A homomorphism of constant label sections extends to all locally
constant sections, including disconnected and nonreduced test schemes. -/
def extendHom (h : G →* (baseTest S ⟶ H)) (T : Over S) :
    LocallyConstant T.left G →* (T ⟶ H) where
  toFun := extend h T
  map_one' := by
    change extend h T (LocallyConstant.const T.left 1) = 1
    rw [extend_const, map_one, MonObj.comp_one]
  map_mul' c d := by
    let p : LocallyConstant T.left (G × G) :=
      ⟨fun x => (c x, d x), c.isLocallyConstant.prodMk d.isLocallyConstant⟩
    apply hom_ext_on_fibers T p
    intro i
    let U := fiberTest T p i
    let j := fiberInclusion T p i
    have hc : c.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const U.left i.1 := by
      apply LocallyConstant.ext
      intro x
      exact congrArg Prod.fst x.property
    have hd : d.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const U.left i.2 := by
      apply LocallyConstant.ext
      intro x
      exact congrArg Prod.snd x.property
    change j ≫ extend h T (c * d) = j ≫ (extend h T c * extend h T d)
    rw [MonObj.comp_mul, ← extend_natural, ← extend_natural, ← extend_natural]
    have hcd : (c * d).comap ⟨j.left, j.left.continuous⟩ =
        LocallyConstant.const U.left (i.1 * i.2) := by
      apply LocallyConstant.ext
      intro x
      exact congrArg₂ (· * ·) (congrArg (fun e : LocallyConstant U.left G => e x) hc)
        (congrArg (fun e : LocallyConstant U.left G => e x) hd)
    rw [hc, hd, hcd, extend_const, extend_const, extend_const, map_mul, MonObj.comp_mul]

def extendNatTrans (h : G →* (baseTest S ⟶ H)) :
    HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⟶ yonedaGrpObj H where
  app T := GrpCat.ofHom (extendHom h T.unop)
  naturality {T U} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro c
    exact extend_natural h f.unop c

/-- Naturality and values on constant sections force this extension.
Equality is checked on the actual open-fiber decomposition. -/
theorem natTrans_ext_on_constants
    {α β : HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⟶ yonedaGrpObj H}
    (h : ∀ c : G, α.app (.op (baseTest S)) (LocallyConstant.const S c) =
      β.app (.op (baseTest S)) (LocallyConstant.const S c)) : α = β := by
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  apply hom_ext_on_fibers T.unop c
  intro i
  let U := fiberTest T.unop c i
  let j := fiberInclusion T.unop c i
  let b := toBase U
  have hc : c.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const U.left i := by
    apply LocallyConstant.ext
    intro x
    exact x.property
  have hjα := ConcreteCategory.congr_hom (α.naturality j.op) c
  have hjβ := ConcreteCategory.congr_hom (β.naturality j.op) c
  change α.app (.op U) (c.comap ⟨j.left, j.left.continuous⟩) = j ≫ α.app T c at hjα
  change β.app (.op U) (c.comap ⟨j.left, j.left.continuous⟩) = j ≫ β.app T c at hjβ
  rw [hc] at hjα hjβ
  have hbα := ConcreteCategory.congr_hom (α.naturality b.op) (LocallyConstant.const S i)
  have hbβ := ConcreteCategory.congr_hom (β.naturality b.op) (LocallyConstant.const S i)
  change α.app (.op U) (LocallyConstant.const U.left i) =
    b ≫ α.app (.op (baseTest S)) (LocallyConstant.const S i) at hbα
  change β.app (.op U) (LocallyConstant.const U.left i) =
    b ≫ β.app (.op (baseTest S)) (LocallyConstant.const S i) at hbβ
  exact hjα.symm.trans (hbα.trans ((congrArg (fun f => b ≫ f) (h i)).trans
    (hbβ.symm.trans hjβ)))

theorem extendNatTrans_unique (h : G →* (baseTest S ⟶ H))
    (α : HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⟶ yonedaGrpObj H)
    (hc : ∀ c : G, α.app (.op (baseTest S)) (LocallyConstant.const S c) = h c) :
    α = extendNatTrans h := by
  apply natTrans_ext_on_constants
  intro c
  change _ = extend h (baseTest S) (LocallyConstant.const S c)
  have hb : toBase (baseTest S) = 𝟙 (baseTest S) := Over.OverMorphism.ext rfl
  have he := extend_const (⇑h) (baseTest S) c
  rw [hb, Category.id_comp] at he
  exact (hc c).trans he.symm

/-- Independence of constant sections on every nonempty test implies
injectivity on all locally constant sections. -/
theorem extendHom_injective (h : G →* (baseTest S ⟶ H))
    (hind : ∀ (U : Over S), Nonempty U.left → ∀ c : G,
      toBase U ≫ h c = 1 → c = 1) (T : Over S) :
    Function.Injective (extendHom h T) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change c = 1
  apply LocallyConstant.ext
  intro t
  let U := fiberTest T c (c t)
  let j := fiberInclusion T c (c t)
  have hu : Nonempty U.left := ⟨⟨t, rfl⟩⟩
  apply hind U hu (c t)
  have hconst : c.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const U.left (c t) := by
    apply LocallyConstant.ext
    intro x
    exact x.property
  have hn := extend_natural (⇑h) j c
  rw [hconst, extend_const] at hn
  have hzero : extend h T c = 1 := hc
  exact hn.trans ((congrArg (fun f : T ⟶ H => j ≫ f) hzero).trans (MonObj.comp_one _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections
