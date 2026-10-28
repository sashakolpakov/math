import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Sections
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups

/-! # Constant Sections -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstantSections.Lifts

noncomputable section

/-!
Construct a morphism from the native constant group scheme from a group
of integral sections. Its group law is checked on the disjoint open
fibers of locally constant labels, including arbitrary test schemes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

variable (S : Scheme.{u}) (G : Type u) [Group G]

def constantLabelSection : G →* (𝟙_ (Over S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :=
  ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (𝟙_ (Over S)))).groupIsoToMulEquiv.symm.toMonoidHom.comp
    { toFun := LocallyConstant.const S
      map_one' := rfl
      map_mul' _ _ := rfl }

theorem constantLabelSection_left (g : G) :
    (constantLabelSection S G g).left = Sigma.ι (fun _ : G => S) g := by
  let i : 𝟙_ (Over S) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G :=
    Over.homMk (Sigma.ι (fun _ : G => S) g) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom g)
  have hi : constantLabelSection S G g = i := by
    apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (𝟙_ (Over S))).injective
    have hlabel : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (𝟙_ (Over S)))
        (constantLabelSection S G g) = LocallyConstant.const S g :=
      ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (.op (𝟙_ (Over S)))).groupIsoToMulEquiv.apply_symm_apply _
    rw [hlabel]
    apply LocallyConstant.ext
    intro x
    exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι g x).symm
  exact congrArg Over.Hom.left hi

variable {S G} {A : Over S} [GrpObj A]

def mapFromConstantSections (s : G →* (𝟙_ (Over S) ⟶ A)) :
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ⟶ A :=
  Over.homMk (Sigma.desc (fun g => (s g).left)) (by
    apply Sigma.hom_ext
    intro g
    erw [Sigma.ι_comp_desc_assoc, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom]
    exact (s g).w)

theorem constantLabelSection_map (s : G →* (𝟙_ (Over S) ⟶ A)) (g : G) :
    constantLabelSection S G g ≫ mapFromConstantSections s = s g := by
  apply Over.OverMorphism.ext
  change (constantLabelSection S G g).left ≫ Sigma.desc (fun g => (s g).left) = _
  erw [constantLabelSection_left, Sigma.ι_comp_desc]

omit [GrpObj A] in
theorem constantMaps_ext (f h : (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ⟶ A)
    (heq : ∀ g, constantLabelSection S G g ≫ f = constantLabelSection S G g ≫ h) : f = h := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro g
  have he := congrArg Over.Hom.left (heq g)
  change (constantLabelSection S G g).left ≫ f.left =
    (constantLabelSection S G g).left ≫ h.left at he
  rw [constantLabelSection_left] at he
  exact he

theorem constantPoint_factor {T : Over S} (a : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) (g : G)
    (ha : ∀ t : T.left, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T a t = g) :
    a = toUnit T ≫ constantLabelSection S G g := by
  apply Over.OverMorphism.ext
  change a.left = T.hom ≫ (constantLabelSection S G g).left
  rw [constantLabelSection_left]
  have h := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_factor a.left g ha
  exact h.trans (congrArg (fun f => f ≫ Sigma.ι (fun _ : G => S) g) a.w)

/-- Multiplication is proved after restricting to disjoint label fibers;
the test scheme may be nonreduced or disconnected. -/
theorem mapFromConstantSections_mul (s : G →* (𝟙_ (Over S) ⟶ A))
    (T : Over S) (a b : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :
    (a * b) ≫ mapFromConstantSections s =
      (a ≫ mapFromConstantSections s) * (b ≫ mapFromConstantSections s) := by
  let c : LocallyConstant T.left (G × G) :=
    ⟨fun t => (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T a t, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T b t),
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T a).isLocallyConstant.prodMk
        (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T b).isLocallyConstant⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso c).hom).mp
  apply Sigma.hom_ext
  intro p
  rw [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc]
  let V : Over S := Over.mk ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c p).ι ≫ T.hom)
  let j : V ⟶ T := Over.homMk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c p).ι rfl
  have ha : j ≫ a = toUnit V ≫ constantLabelSection S G p.1 := by
    apply constantPoint_factor
    intro t
    exact congrArg Prod.fst t.property
  have hb : j ≫ b = toUnit V ≫ constantLabelSection S G p.2 := by
    apply constantPoint_factor
    intro t
    exact congrArg Prod.snd t.property
  have hab : j ≫ (a * b) = toUnit V ≫ constantLabelSection S G (p.1 * p.2) := by
    rw [MonObj.comp_mul, ha, hb, ← MonObj.comp_mul, ← map_mul]
  have h : j ≫ ((a * b) ≫ mapFromConstantSections s) =
      j ≫ ((a ≫ mapFromConstantSections s) * (b ≫ mapFromConstantSections s)) := by
    rw [← Category.assoc, hab, Category.assoc, constantLabelSection_map,
      MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ha, hb,
      Category.assoc, Category.assoc, constantLabelSection_map, constantLabelSection_map,
      ← MonObj.comp_mul, map_mul]
  exact congrArg Over.Hom.left h

instance mapFromConstantSections_isMonHom (s : G →* (𝟙_ (Over S) ⟶ A)) :
    IsMonHom (mapFromConstantSections s) where
  one_hom := by
    change (1 : 𝟙_ (Over S) ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) ≫ mapFromConstantSections s = 1
    rw [← (constantLabelSection S G).map_one, constantLabelSection_map, s.map_one]
  mul_hom := by
    have h := mapFromConstantSections_mul s
      ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X)
      (fst _ _) (snd _ _)
    have he : lift (fst (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ≫ mapFromConstantSections s)
        (snd (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X ≫ mapFromConstantSections s) =
        mapFromConstantSections s ⊗ₘ mapFromConstantSections s := by
      apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd,
        tensorHom_fst, tensorHom_snd]
    simpa only [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp, he] using h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstantSections.Lifts
