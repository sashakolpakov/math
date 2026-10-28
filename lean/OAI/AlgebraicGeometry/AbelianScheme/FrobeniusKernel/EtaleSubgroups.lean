import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Etale Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

noncomputable section

/-!
Actual finite étale group schemes used for the chosen active étale lines.
The schemes are disjoint unions of the base; their group structure and
subgroup maps are reconstructed from all locally constant test sections.
These models are used only for the étale ordinary factors.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

def etaleGroupRepresentable (S : Scheme.{u}) (G : Type u) [Group G] :
    (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⋙ forget GrpCat).RepresentableBy (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) where
  homEquiv := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G _
  homEquiv_comp h t := by
    apply LocallyConstant.ext
    intro x
    rfl

/-- The native finite constant group scheme for an étale label group. -/
def etaleGroupScheme (S : Scheme.{u}) (G : Type u) [Group G] : Grp (Over S) := by
  letI : GrpObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) := GrpObj.ofRepresentableBy (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G)
    (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G) (etaleGroupRepresentable S G)
  exact Grp.mk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G)

def etaleGroupPointIso (S : Scheme.{u}) (G : Type u) [Group G] :
    yonedaGrp.obj (etaleGroupScheme S G) ≅ AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G :=
  yonedaGrpObjIsoOfRepresentableBy (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G)
    (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G) (etaleGroupRepresentable S G)

instance etaleGroupScheme_finite (S : Scheme.{u}) (G : Type u) [Group G] [Finite G] :
    IsFinite (etaleGroupScheme S G).X.hom := AbelianModuli.HilbertConstruction.Finite.ConstantScheme.constantScheme_finite

instance etaleGroupScheme_etale (S : Scheme.{u}) (G : Type u) [Group G] :
    Etale (etaleGroupScheme S G).X.hom := AbelianModuli.HilbertConstruction.Level.Scheme.constantScheme_etale S G

/-- A homomorphism of étale labels induces an actual group-scheme map. -/
def etaleGroupMap (S : Scheme.{u}) {G H : Type u} [Group G] [Group H] (f : G →* H) :
    etaleGroupScheme S G ⟶ etaleGroupScheme S H :=
  (yonedaGrpFullyFaithful (C := Over S)).preimage
    ((etaleGroupPointIso S G).hom ≫
      AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMapOfLabels (LocallyConstant.const S f) ≫ (etaleGroupPointIso S H).inv)

theorem etaleGroupMap_sections (S : Scheme.{u}) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (T : Over S) (a : T ⟶ (etaleGroupScheme S G).X) (x : T.left) :
    LocallyConstant.toFun ((etaleGroupPointIso S H).hom.app (.op T)
      (a ≫ (etaleGroupMap S f).hom.hom)) x =
      f (LocallyConstant.toFun ((etaleGroupPointIso S G).hom.app (.op T) a) x) := by
  have h := (yonedaGrpFullyFaithful (C := Over S)).map_preimage
    ((etaleGroupPointIso S G).hom ≫
      AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMapOfLabels (LocallyConstant.const S f) ≫ (etaleGroupPointIso S H).inv)
  have hc := congrArg (fun α => α ≫ (etaleGroupPointIso S H).hom) h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  have ha := congrArg (fun α => (α.app (.op T)).hom a) hc
  exact congrArg (fun c : LocallyConstant T.left H => c x) ha

theorem etaleGroupMap_mono (S : Scheme.{u}) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) : Mono (etaleGroupMap S f).hom.hom where
  right_cancellation a b hab := by
    apply ((etaleGroupPointIso S G).app (.op _)).groupIsoToMulEquiv.injective
    apply LocallyConstant.ext
    intro x
    apply hf
    exact (etaleGroupMap_sections S f _ a x).symm.trans
      ((congrArg (fun c => LocallyConstant.toFun
        ((etaleGroupPointIso S H).hom.app (.op _) c) x) hab).trans
        (etaleGroupMap_sections S f _ b x))

/-- The active étale q-torsion plane has its literal rank-two label space. -/
abbrev ActiveEtalePlane (q : ℕ) := Fin 2 → ZMod q

/-- Lines are actual submodules, with each submodule occurring once. -/
def ActiveEtaleLine (q : ℕ) [Fact q.Prime] :=
  {L : Submodule (ZMod q) (ActiveEtalePlane q) // Module.finrank (ZMod q) L = 1}

instance activeEtaleLine_finite (q : ℕ) [Fact q.Prime] : Finite (ActiveEtaleLine q) := by
  unfold ActiveEtaleLine
  infer_instance

def activeEtaleLineLabels (q : ℕ) [Fact q.Prime] (L : ActiveEtaleLine q) :
    Multiplicative L.val →* Multiplicative (ActiveEtalePlane q) where
  toFun x := Multiplicative.ofAdd x.toAdd.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem activeEtaleLineLabels_injective (q : ℕ) [Fact q.Prime] (L : ActiveEtaleLine q) :
    Function.Injective (activeEtaleLineLabels q L) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd h

/-- Finite injective label maps give closed embeddings of actual schemes. -/
theorem etaleGroupMap_closed (S : Scheme.{u}) {G H : Type u} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Injective f) :
    IsClosedImmersion (etaleGroupMap S f).hom.hom.left := by
  let a := (etaleGroupMap S f).hom.hom
  have : Mono a := etaleGroupMap_mono S f hf
  have : IsFinite (a.left ≫ (etaleGroupScheme S H).X.hom) :=
    (congrArg IsFinite a.w).mpr (etaleGroupScheme_finite S G)
  have : IsFinite a.left := IsFinite.of_comp a.left (etaleGroupScheme S H).X.hom
  exact (IsClosedImmersion.iff_isFinite_and_mono a.left).mpr ⟨inferInstance, inferInstance⟩

def liftedActiveEtaleLineLabels (q : ℕ) [Fact q.Prime] (L : ActiveEtaleLine q) :
    ULift.{u} (Multiplicative L.val) →* ULift.{u} (Multiplicative (ActiveEtalePlane q)) where
  toFun x := ⟨activeEtaleLineLabels q L x.down⟩
  map_one' := by apply ULift.ext; exact (activeEtaleLineLabels q L).map_one
  map_mul' x y := by apply ULift.ext; exact (activeEtaleLineLabels q L).map_mul x.down y.down

theorem liftedActiveEtaleLineLabels_injective (q : ℕ) [Fact q.Prime]
    (L : ActiveEtaleLine q) : Function.Injective (liftedActiveEtaleLineLabels.{u} q L) := by
  intro x y h
  apply ULift.ext
  apply activeEtaleLineLabels_injective q L
  exact congrArg ULift.down h

def activeEtalePlaneScheme (S : Scheme.{u}) (q : ℕ) : Grp (Over S) :=
  etaleGroupScheme S (ULift.{u} (Multiplicative (ActiveEtalePlane q)))

def activeEtaleLineScheme (S : Scheme.{u}) (q : ℕ) [Fact q.Prime]
    (L : ActiveEtaleLine q) : Grp (Over S) :=
  etaleGroupScheme S (ULift.{u} (Multiplicative L.val))

/-- The chosen line is embedded in the active étale q-torsion plane. -/
def activeEtaleLineEmbedding (S : Scheme.{u}) (q : ℕ) [Fact q.Prime]
    (L : ActiveEtaleLine q) : activeEtaleLineScheme S q L ⟶ activeEtalePlaneScheme S q :=
  etaleGroupMap S (liftedActiveEtaleLineLabels q L)

theorem activeEtaleLineEmbedding_closed (S : Scheme.{u}) (q : ℕ) [Fact q.Prime]
    (L : ActiveEtaleLine q) : IsClosedImmersion (activeEtaleLineEmbedding S q L).hom.hom.left :=
  etaleGroupMap_closed S (liftedActiveEtaleLineLabels q L)
    (liftedActiveEtaleLineLabels_injective q L)

theorem activeEtaleLineScheme_finiteLocallyFree (S : Scheme.{u}) (q : ℕ) [Fact q.Prime]
    (L : ActiveEtaleLine q) :
    IsFinite (activeEtaleLineScheme S q L).X.hom ∧
      Flat (activeEtaleLineScheme S q L).X.hom ∧
      LocallyOfFinitePresentation (activeEtaleLineScheme S q L).X.hom := by
  have : Etale (activeEtaleLineScheme S q L).X.hom := etaleGroupScheme_etale S _
  exact ⟨etaleGroupScheme_finite S _, inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction
