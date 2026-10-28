import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # PEL Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Base change of actual marked polarized isogenies. The Poincare
identity is transported through the natural product comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

variable {S T : Scheme.{u}}

theorem PELBaseChange.pullback_map_pow {A B : Over S} [MonObj B] (s : T ⟶ S) (f : A ⟶ B) (n : ℕ) :
    (Over.pullback s).map (f ^ n) = ((Over.pullback s).map f) ^ n := by
  induction n with
  | zero => exact (Over.pullback s).map_one
  | succ n ih => rw [pow_succ, (Over.pullback s).map_mul, ih, pow_succ]

def PELBaseChange.baseChangeProductMap (A B : Over S) (s : T ⟶ S) :
    (((Over.pullback s).obj A) ⊗ ((Over.pullback s).obj B)).left ⟶ (A ⊗ B).left :=
  (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s

theorem PELBaseChange.baseChangeProductMap_natural {A B A' B' : Over S}
    (f : A ⟶ A') (g : B ⟶ B') (s : T ⟶ S) :
    ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map g).left ≫
      PELBaseChange.baseChangeProductMap A' B' s = PELBaseChange.baseChangeProductMap A B s ≫ (f ⊗ₘ g).left := by
  unfold PELBaseChange.baseChangeProductMap
  rw [← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural, Over.comp_left,
    Category.assoc, AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc]

theorem PELBaseChange.pullback_tensor_class {A B A' B' : Over S}
    (f : A ⟶ A') (g : B ⟶ B') (s : T ⟶ S) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A' ⊗ B').left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map g).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap A' B' s) c) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap A B s)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ g).left c) := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, PELBaseChange.baseChangeProductMap_natural, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]

theorem PELBaseChange.poincareClass_pullback {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : T ⟶ S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback s).poincare =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap D.abelian.scheme A.scheme s)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap s).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) = _
  rw [← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
  rfl

variable {R : Type u} [CommRing R] {g N : ℕ}

theorem PELBaseChange.fullLevel_pullback_basis {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (level : A.FullLevel N)
    (s : T ⟶ S) (U : Over T)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.baseChangePointsEquiv s U ((level.pullback s).hom.app (.op U) c).val =
      (level.hom.app (.op ((Over.map s).obj U)) c).val :=
  congrArg (fun x : A.torsionPoints N ((Over.map s).obj U) => x.val)
    ((A.torsionBaseChangeEquiv s U N).apply_symm_apply
      (level.hom.app (.op ((Over.map s).obj U)) c))

section

variable {A B : PEL.PELFamilyData R g N S} {n : ℕ}

def PELIsogenies.PELIsogeny.pullback (e : PELIsogenies.PELIsogeny A B n) (s : T ⟶ S) :
    PELIsogenies.PELIsogeny (A.pullback s) (B.pullback s) n where
  isogeny := e.isogeny.pullback s
  dualHom := (Over.pullback s).map e.dualHom
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback s).map e.dualHom))
  poincare := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (𝟙 (B.dual.abelian.pullback s).scheme ⊗ₘ (Over.pullback s).map e.isogeny.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.dual.poincarePullbackOverMap s).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        ((Over.pullback s).map e.dualHom ⊗ₘ 𝟙 (A.abelian.pullback s).scheme).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap s).left
            (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare))
    rw [← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap, ← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (𝟙 ((Over.pullback s).obj B.dual.abelian.scheme) ⊗ₘ (Over.pullback s).map e.isogeny.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap B.dual.abelian.scheme B.abelian.scheme s)
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        ((Over.pullback s).map e.dualHom ⊗ₘ 𝟙 ((Over.pullback s).obj A.abelian.scheme)).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap A.dual.abelian.scheme A.abelian.scheme s)
            (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare))
    rw [
      ← (Over.pullback s).map_id B.dual.abelian.scheme,
      ← (Over.pullback s).map_id A.abelian.scheme,
      PELBaseChange.pullback_tensor_class, PELBaseChange.pullback_tensor_class, e.poincare]
  equivariant r := by
    exact (congrArg (fun z => z ≫ (Over.pullback s).map e.isogeny.hom)
      (A.pullback_action_schemeMap s r)).trans
        (((Over.pullback s).map_comp _ _).symm.trans
          ((congrArg (fun z => (Over.pullback s).map z) (e.equivariant r)).trans
            (((Over.pullback s).map_comp _ _).trans
              (congrArg (fun z => (Over.pullback s).map e.isogeny.hom ≫ z)
                (B.pullback_action_schemeMap s r).symm))))
  polarization := by
    change (Over.pullback s).map e.isogeny.hom ≫ (Over.pullback s).map B.polarizationMap.hom ≫
      (Over.pullback s).map e.dualHom = ((Over.pullback s).map A.polarizationMap.hom) ^ n
    rw [← (Over.pullback s).map_comp, ← (Over.pullback s).map_comp, e.polarization]
    exact PELBaseChange.pullback_map_pow s _ n
  marking U c := by
    apply (B.abelian.baseChangePointsEquiv s U).injective
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map e.isogeny.hom s U
      ((A.marking.pullback s).hom.app (.op U) c).val).trans
        ((congrArg (fun z => z ≫ e.isogeny.hom) (PELBaseChange.fullLevel_pullback_basis A.marking s U c)).trans
          ((e.marking ((Over.map s).obj U) c).trans (PELBaseChange.fullLevel_pullback_basis B.marking s U c).symm))

@[simp]
theorem PELIsogenies.PELIsogeny.pullback_hom (e : PELIsogenies.PELIsogeny A B n) (s : T ⟶ S) :
    (e.pullback s).isogeny.hom = (Over.pullback s).map e.isogeny.hom := rfl

end

variable {A B : PEL.PELFamilyData R g N S}

def PELModuli.PELFamilyIso.pullback (e : PELModuli.PELFamilyIso A B) (s : T ⟶ S) :
    PELModuli.PELFamilyIso (A.pullback s) (B.pullback s) where
  abelian := (Over.pullback s).mapIso e.abelian
  dual := (Over.pullback s).mapIso e.dual
  abelianGroup := inferInstanceAs (IsMonHom ((Over.pullback s).map e.abelian.hom))
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback s).map e.dual.hom))
  polarization := by
    change (Over.pullback s).map A.polarizationMap.hom ≫ (Over.pullback s).map e.dual.hom =
      (Over.pullback s).map e.abelian.hom ≫ (Over.pullback s).map B.polarizationMap.hom
    rw [← (Over.pullback s).map_comp, ← (Over.pullback s).map_comp, e.polarization]
  poincare := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback s).map e.dual.hom ⊗ₘ
      (Over.pullback s).map e.abelian.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.dual.poincarePullbackOverMap s).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap s).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)
    rw [← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap, ← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
    exact (PELBaseChange.pullback_tensor_class e.dual.hom e.abelian.hom s (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).trans
      (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PELBaseChange.baseChangeProductMap A.dual.abelian.scheme A.abelian.scheme s))
        e.poincare)
  equivariant r := by
    exact (congrArg (fun z => z ≫ (Over.pullback s).map e.abelian.hom)
      (A.pullback_action_schemeMap s r)).trans
        (((Over.pullback s).map_comp _ _).symm.trans
          ((congrArg (fun z => (Over.pullback s).map z) (e.equivariant r)).trans
            (((Over.pullback s).map_comp _ _).trans
              (congrArg (fun z => (Over.pullback s).map e.abelian.hom ≫ z)
                (B.pullback_action_schemeMap s r).symm))))
  marking U c := by
    apply (B.abelian.baseChangePointsEquiv s U).injective
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map e.abelian.hom s U
      ((A.marking.pullback s).hom.app (.op U) c).val).trans
        ((congrArg (fun z => z ≫ e.abelian.hom) (PELBaseChange.fullLevel_pullback_basis A.marking s U c)).trans
          ((e.marking ((Over.map s).obj U) c).trans (PELBaseChange.fullLevel_pullback_basis B.marking s U c).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
