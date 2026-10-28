import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Acyclic Models F -/

namespace OAI.AlgebraicTopology.Kunneth.AcyclicModelsF

noncomputable section

/-!
The acyclic-model lifting argument needed to compare product singular
chains with tensor products of singular chains in Kunneth. A presentation here
is an actual coproduct of free representable functors. Exactness is required
only after evaluation on the displayed models.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction.AcyclicModels

variable {k : Type} [Field k]
variable {J : Type 1} [Category.{0} J]

abbrev FreeModel (M : J) : J ⥤ ModuleCat.{0} k :=
  (evaluationLeftAdjoint (ModuleCat.{0} k) M).obj (ModuleCat.of k k)

/-- A concrete free presentation of a functor by its models. -/
structure Presentation (F : J ⥤ ModuleCat.{0} k) where
  Index : Type
  model : Index → J
  iso : (∐ fun i => FreeModel (k := k) (model i)) ≅ F

namespace Presentation

/-- A single free representable functor is a presentation with one model. -/
def ofSingle {F : J ⥤ ModuleCat.{0} k} (M : J)
    (e : FreeModel (k := k) M ≅ F) : Presentation F where
  Index := PUnit
  model _ := M
  iso :=
    { hom := Sigma.desc (fun _ : PUnit => e.hom)
      inv := e.inv ≫ Sigma.ι (fun _ : PUnit => FreeModel (k := k) M) PUnit.unit
      hom_inv_id := by
        apply Sigma.hom_ext
        intro i
        cases i
        simp only [Sigma.ι_comp_desc_assoc, Iso.hom_inv_id_assoc, Category.comp_id]
      inv_hom_id := by simp }

variable {F : J ⥤ ModuleCat.{0} k} (P : Presentation F)

def generator (i : P.Index) : FreeModel (k := k) (P.model i) ⟶ F :=
  Sigma.ι (fun i => FreeModel (k := k) (P.model i)) i ≫ P.iso.hom

/-- Lifting through an exact sequence on each model suffices for lifting
 a natural map out of the presented functor. -/
def lift (S : ShortComplex (J ⥤ ModuleCat.{0} k))
    (hS : ∀ i, (S.map ((evaluation J (ModuleCat.{0} k)).obj (P.model i))).Exact)
    (f : F ⟶ S.X₂) (hf : f ≫ S.g = 0) : F ⟶ S.X₁ := by
  let adj (i : P.Index) := evaluationAdjunctionRight (ModuleCat.{0} k) (P.model i)
  let a (i : P.Index) : ModuleCat.of k k ⟶ S.X₂.obj (P.model i) :=
    (adj i).homEquiv _ _ (P.generator i ≫ f)
  have ha (i : P.Index) : a i ≫ S.g.app (P.model i) = 0 := by
    change Sigma.ι (fun _ : P.model i ⟶ P.model i => ModuleCat.of k k)
      (𝟙 (P.model i)) ≫ (P.generator i ≫ f).app (P.model i) ≫
        S.g.app (P.model i) = 0
    rw [← NatTrans.comp_app, Category.assoc, hf, comp_zero, zero_app, comp_zero]
  let b (i : P.Index) : ModuleCat.of k k ⟶ S.X₁.obj (P.model i) :=
    (hS i).liftFromProjective (a i) (ha i)
  exact P.iso.inv ≫ Sigma.desc (fun i => (adj i).homEquiv _ _ |>.symm <| b i)

@[reassoc (attr := simp)]
theorem lift_comp (S : ShortComplex (J ⥤ ModuleCat.{0} k))
    (hS : ∀ i, (S.map ((evaluation J (ModuleCat.{0} k)).obj (P.model i))).Exact)
    (f : F ⟶ S.X₂) (hf : f ≫ S.g = 0) :
    P.lift S hS f hf ≫ S.f = f := by
  apply (cancel_epi P.iso.hom).mp
  apply Sigma.hom_ext
  intro i
  dsimp [Presentation.lift]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc_assoc]
  apply ((evaluationAdjunctionRight (ModuleCat.{0} k) (P.model i)).homEquiv
    (ModuleCat.of k k) S.X₂).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  exact (hS i).liftFromProjective_comp _ _

end Presentation

variable (P Q : ChainComplex (J ⥤ ModuleCat.{0} k) ℕ)
variable (models : ∀ n, Presentation (P.X n))
variable (hQ : ∀ (n : ℕ) (i : (models n).Index) (q : ℕ),
  ((Q.sc' (q + 2) (q + 1) q).map
    ((evaluation J (ModuleCat.{0} k)).obj ((models n).model i))).Exact)

/-- Extend compatible maps in degrees zero and one to a natural chain map. -/
def extendChainMap (f0 : P.X 0 ⟶ Q.X 0) (f1 : P.X 1 ⟶ Q.X 1)
    (hf : f1 ≫ Q.d 1 0 = P.d 1 0 ≫ f0) : P ⟶ Q :=
  ChainComplex.mkHom P Q f0 f1 hf (fun n p => by
    rcases p with ⟨u, v, hv⟩
    have hc : (P.d (n + 2) (n + 1) ≫ v) ≫ Q.d (n + 1) n = 0 := by
      rw [Category.assoc, hv, ← Category.assoc, P.d_comp_d, zero_comp]
    exact ⟨(models (n + 2)).lift (Q.sc' (n + 2) (n + 1) n)
      (fun i => hQ (n + 2) i n) _ hc, (models (n + 2)).lift_comp _ _ _ _⟩)

@[simp]
theorem extendChainMap_f_zero (f0 : P.X 0 ⟶ Q.X 0) (f1 : P.X 1 ⟶ Q.X 1)
    (hf : f1 ≫ Q.d 1 0 = P.d 1 0 ≫ f0) :
    (extendChainMap P Q models hQ f0 f1 hf).f 0 = f0 := rfl

@[simp]
theorem extendChainMap_f_one (f0 : P.X 0 ⟶ Q.X 0) (f1 : P.X 1 ⟶ Q.X 1)
    (hf : f1 ≫ Q.d 1 0 = P.d 1 0 ≫ f0) :
    (extendChainMap P Q models hQ f0 f1 hf).f 1 = f1 := rfl

/-- Natural chain maps agreeing in degree zero are naturally homotopic. -/
def nullhomotopy (e : P ⟶ Q) (he : e.f 0 = 0) : Homotopy e 0 := by
  have hc : e.f 1 ≫ Q.d 1 0 = 0 := by rw [e.comm 1 0, he, comp_zero]
  let h1 := (models 1).lift (Q.sc' 2 1 0) (fun i => hQ 1 i 0) (e.f 1) hc
  have h1eq : h1 ≫ Q.d 2 1 = e.f 1 := (models 1).lift_comp _ _ _ _
  refine Homotopy.mkInductive e 0 ?_ h1 ?_ ?_
  · simpa only [zero_comp] using he
  · simpa only [comp_zero, zero_add] using h1eq.symm
  · intro n p
    rcases p with ⟨u, v, hv⟩
    let a := e.f (n + 2) - P.d (n + 2) (n + 1) ≫ v
    have ha : a ≫ Q.d (n + 2) (n + 1) = 0 := by
      dsimp only [a]
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hv, Preadditive.comp_add]
      simp only [← Category.assoc, P.d_comp_d, zero_comp, zero_add, sub_self]
    refine ⟨(models (n + 2)).lift (Q.sc' (n + 3) (n + 2) (n + 1))
      (fun i => hQ (n + 2) i (n + 1)) a ha, ?_⟩
    have hb : (models (n + 2)).lift (Q.sc' (n + 3) (n + 2) (n + 1))
        (fun i => hQ (n + 2) i (n + 1)) a ha ≫ Q.d (n + 3) (n + 2) = a :=
      (models (n + 2)).lift_comp _ _ _ _
    calc
      e.f (n + 2) = P.d (n + 2) (n + 1) ≫ v + a := by dsimp [a]; abel
      _ = _ := congrArg (fun w => P.d (n + 2) (n + 1) ≫ v + w) hb.symm

def homotopy (f g : P ⟶ Q) (hfg : f.f 0 = g.f 0) : Homotopy f g :=
  Homotopy.equivSubZero.symm (nullhomotopy P Q models hQ (f - g) (by
    change f.f 0 - g.f 0 = 0
    rw [hfg, sub_self]))

end Construction.AcyclicModels

end

end OAI.AlgebraicTopology.Kunneth.AcyclicModelsF
