import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.LocallyConstant.Basic

/-! # Iff -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

noncomputable section

/-! Constant schemes and the disjoint open decomposition attached to a locally constant map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.TopologicalSpace

universe u

variable {I : Type u} {S T : Scheme.{u}}

/-- The disjoint union of one copy of the base for each element of an index type. -/
def constantScheme (S : Scheme.{u}) (I : Type u) : Over S :=
  Over.mk (Sigma.desc (fun _ : I => 𝟙 S))

@[simp, reassoc]
theorem constantScheme_ι_hom (i : I) :
    Sigma.ι (fun _ : I => S) i ≫ (constantScheme S I).hom = 𝟙 S :=
  Sigma.ι_comp_desc _ _

/-- The index of a point in a disjoint union is locally constant. -/
def constantSchemeIndex (S : Scheme.{u}) (I : Type u) :
    LocallyConstant (constantScheme S I).left I where
  toFun x := ((sigmaMk (fun _ : I => S)).symm x).1
  isLocallyConstant :=
    (show IsLocallyConstant (Sigma.fst : (Σ _ : I, S) → I) from
      isOpen_sigma_fst_preimage).comp_continuous (sigmaMk (fun _ : I => S)).symm.continuous

@[simp]
theorem constantSchemeIndex_ι (i : I) (x : S) :
    constantSchemeIndex S I (Sigma.ι (fun _ : I => S) i x) = i := by
  change ((sigmaMk (fun _ : I => S)).symm (Sigma.ι (fun _ : I => S) i x)).1 = i
  rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

/-- The index-valued locally constant function associated with a map to a constant scheme. -/
def constantSchemePoint (T : Over S) (f : T ⟶ constantScheme S I) :
    LocallyConstant T.left I :=
  (constantSchemeIndex S I).comap ⟨f.left, f.left.continuous⟩

/-- A fiber of a locally constant map is an open subscheme. -/
def locallyConstantFiber (c : LocallyConstant T I) (i : I) : T.Opens :=
  ⟨{x | c x = i}, c.isLocallyConstant.isOpen_fiber i⟩

/-- The open fibers of a locally constant function form a disjoint-union presentation. -/
instance locallyConstantFibersDesc_isIso (c : LocallyConstant T I) :
    IsIso (Sigma.desc (fun i => (locallyConstantFiber c i).ι)) := by
  apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk T (fun i => (locallyConstantFiber c i).ι))).mp
  apply nonempty_isColimit_cofanMk_of
  · simp only [Scheme.Opens.opensRange_ι]
    apply top_unique
    intro x _
    exact (Opens.mem_iSup).mpr ⟨c x, rfl⟩
  · intro i j hij
    change Disjoint (locallyConstantFiber c i).ι.opensRange (locallyConstantFiber c j).ι.opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    exact (hij (hx.1.symm.trans hx.2)).elim

/-- The domain is canonically the disjoint union of the fibers of a locally constant map. -/
def locallyConstantFibersIso (c : LocallyConstant T I) :
    (∐ fun i => (locallyConstantFiber c i).toScheme) ≅ T :=
  asIso (Sigma.desc (fun i => (locallyConstantFiber c i).ι))

@[simp, reassoc]
theorem locallyConstantFibersIso_ι_hom (c : LocallyConstant T I) (i : I) :
    Sigma.ι (fun i => (locallyConstantFiber c i).toScheme) i ≫
        (locallyConstantFibersIso c).hom = (locallyConstantFiber c i).ι :=
  Sigma.ι_comp_desc _ _

@[simp, reassoc]
theorem locallyConstantFibersIso_ι_inv (c : LocallyConstant T I) (i : I) :
    (locallyConstantFiber c i).ι ≫ (locallyConstantFibersIso c).inv =
      Sigma.ι (fun i => (locallyConstantFiber c i).toScheme) i :=
  (Iso.comp_inv_eq _).mpr (locallyConstantFibersIso_ι_hom c i).symm

/-- A point has index `i` exactly when it lies in the `i`th copy of the base. -/
theorem constantSchemeIndex_eq_iff (x : (constantScheme S I).left) (i : I) :
    constantSchemeIndex S I x = i ↔ x ∈ Set.range (Sigma.ι (fun _ : I => S) i) := by
  constructor
  · intro hx
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk (fun _ : I => S)).surjective x
    rw [sigmaMk_mk, constantSchemeIndex_ι] at hx
    subst j
    exact ⟨y, (sigmaMk_mk (fun _ : I => S) i y).symm⟩
  · rintro ⟨y, rfl⟩
    exact constantSchemeIndex_ι i y

/-- A map with constant index factors through the corresponding copy of the base. -/
theorem constantScheme_factor (f : T ⟶ (constantScheme S I).left) (i : I)
    (hf : ∀ x, constantSchemeIndex S I (f x) = i) :
    f = (f ≫ (constantScheme S I).hom) ≫ Sigma.ι (fun _ : I => S) i := by
  have : IsOpenImmersion (Sigma.ι (fun _ : I => S) i) := inferInstance
  have hr : Set.range f ⊆ Set.range (Sigma.ι (fun _ : I => S) i) := by
    rintro _ ⟨x, rfl⟩
    exact (constantSchemeIndex_eq_iff (f x) i).mp (hf x)
  let l := IsOpenImmersion.lift (Sigma.ι (fun _ : I => S) i) f hr
  have hl : l ≫ Sigma.ι (fun _ : I => S) i = f :=
    IsOpenImmersion.lift_fac (Sigma.ι (fun _ : I => S) i : S ⟶ ∐ fun _ : I => S) f hr
  have hb : l = f ≫ (constantScheme S I).hom :=
    (Category.comp_id l).symm.trans
      ((congrArg (fun z => l ≫ z) (constantScheme_ι_hom (S := S) i).symm).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun z => z ≫ (constantScheme S I).hom) hl)))
  exact hl.symm.trans (congrArg (fun z => z ≫ Sigma.ι (fun _ : I => S) i) hb)

/-- A locally constant index function determines a map into the disjoint union of bases. -/
def constantSchemePointInverse (T : Over S) (c : LocallyConstant T.left I) :
    T ⟶ constantScheme S I :=
  Over.homMk ((locallyConstantFibersIso c).inv ≫
    Sigma.desc (fun i => (locallyConstantFiber c i).ι ≫ T.hom ≫ Sigma.ι (fun _ : I => S) i)) (by
      have hd : (Sigma.desc (fun i =>
          (locallyConstantFiber c i).ι ≫ T.hom ≫ Sigma.ι (fun _ : I => S) i)) ≫
          (constantScheme S I).hom = (locallyConstantFibersIso c).hom ≫ T.hom := by
        apply Sigma.hom_ext
        intro i
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (constantScheme S I).hom) (Sigma.ι_comp_desc _ _)).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun z => (locallyConstantFiber c i).ι ≫ z)
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun z => T.hom ≫ z) (constantScheme_ι_hom i)).trans
                    (Category.comp_id _)))).trans
                (locallyConstantFibersIso_ι_hom_assoc c i T.hom).symm)))
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => (locallyConstantFibersIso c).inv ≫ z) hd).trans
          ((locallyConstantFibersIso c).inv_hom_id_assoc T.hom)))

@[reassoc]
theorem constantSchemePointInverse_ι (T : Over S) (c : LocallyConstant T.left I) (i : I) :
    (locallyConstantFiber c i).ι ≫ (constantSchemePointInverse T c).left =
      (locallyConstantFiber c i).ι ≫ T.hom ≫ Sigma.ι (fun _ : I => S) i :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ Sigma.desc (fun j =>
      (locallyConstantFiber c j).ι ≫ T.hom ≫ Sigma.ι (fun _ : I => S) j))
      (locallyConstantFibersIso_ι_inv c i)).trans (Sigma.ι_comp_desc _ _))

theorem constantSchemePoint_rightInverse (T : Over S) (c : LocallyConstant T.left I) :
    constantSchemePoint T (constantSchemePointInverse T c) = c := by
  ext x
  let y : (locallyConstantFiber c (c x)).toScheme := ⟨x, rfl⟩
  have w := congrArg (fun z : (locallyConstantFiber c (c x)).toScheme ⟶
    (constantScheme S I).left => z y) (constantSchemePointInverse_ι T c (c x))
  change (constantSchemePointInverse T c).left x =
    Sigma.ι (fun _ : I => S) (c x) (T.hom x) at w
  change constantSchemeIndex S I ((constantSchemePointInverse T c).left x) = c x
  rw [w, constantSchemeIndex_ι]

theorem constantSchemePoint_leftInverse (T : Over S) (f : T ⟶ constantScheme S I) :
    constantSchemePointInverse T (constantSchemePoint T f) = f := by
  let c := constantSchemePoint T f
  apply Over.OverMorphism.ext
  apply (cancel_epi (locallyConstantFibersIso c).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [locallyConstantFibersIso_ι_hom_assoc, locallyConstantFibersIso_ι_hom_assoc]
  have hfactor := constantScheme_factor ((locallyConstantFiber c i).ι ≫ f.left) i
    (fun x => x.property)
  exact (constantSchemePointInverse_ι T c i).trans
    ((congrArg (fun z => z ≫ Sigma.ι (fun _ : I => S) i)
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (locallyConstantFiber c i).ι ≫ z) f.w)).symm).trans hfactor.symm)

/-- Maps over the base into a constant scheme are exactly locally constant index functions. -/
def constantSchemePointsEquiv (S : Scheme.{u}) (I : Type u) (T : Over S) :
    (T ⟶ constantScheme S I) ≃ LocallyConstant T.left I where
  toFun := constantSchemePoint T
  invFun := constantSchemePointInverse T
  left_inv := constantSchemePoint_leftInverse T
  right_inv := constantSchemePoint_rightInverse T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff
