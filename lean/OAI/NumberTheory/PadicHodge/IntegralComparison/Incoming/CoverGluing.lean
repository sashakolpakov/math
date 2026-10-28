import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverFamily

/-! # Cover Gluing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverGluing

noncomputable section

/-!
# IntegralComparison: gluing compatible sections across a covering family of incoming full subsites
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverFamily.Family

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) {ι : Type z} (P : ι → ObjectProperty C)
  (hP : ∀ i {U V : C}, (U ⟶ V) → P i V → P i U)
  (Q : ObjectProperty C) (J : GrothendieckTopology C)
  (hcover : ∀ T, Q T → CoverFamily.Family.sieve P hP T ∈ J T)
  (F : Sheaf J (ModuleCat.{w} R)) (a : ∀ i, SectionRestriction.Sections R M (P i) F.obj)
  (ha : CoverFamily.Family.Compatible R M P F.obj a)

def glueAt (T : C) (hT : Q T) : M ⟶ F.obj.obj (op T) :=
  (F.property M (CoverFamily.Family.sieve P hP T) (hcover T hT)).amalgamate
    (CoverFamily.Family.family R M P hP F.obj a T) (CoverFamily.Family.family_compatible R M P hP F.obj a ha T)

theorem glueAt_restrict (T : C) (hT : Q T) {U : C} (α : U ⟶ T) (hU : ∃ i, P i U) :
    glueAt R M P hP Q J hcover F a ha T hT ≫ F.obj.map α.op = CoverFamily.Family.value R M P F.obj a U hU :=
  (F.property M (CoverFamily.Family.sieve P hP T) (hcover T hT)).valid_glue
    (CoverFamily.Family.family_compatible R M P hP F.obj a ha T) α hU

theorem glueAt_natural {U T : C} (α : U ⟶ T) (hU : Q U) (hT : Q T) :
    glueAt R M P hP Q J hcover F a ha T hT ≫ F.obj.map α.op =
      glueAt R M P hP Q J hcover F a ha U hU := by
  apply (F.property M (CoverFamily.Family.sieve P hP U) (hcover U hU)).isSeparatedFor.ext
  intro W β hβ
  change (glueAt R M P hP Q J hcover F a ha T hT ≫ F.obj.map α.op) ≫ F.obj.map β.op =
    glueAt R M P hP Q J hcover F a ha U hU ≫ F.obj.map β.op
  rw [Category.assoc, ← F.obj.map_comp, ← op_comp]
  exact (glueAt_restrict R M P hP Q J hcover F a ha T hT (β ≫ α) hβ).trans
    (glueAt_restrict R M P hP Q J hcover F a ha U hU β hβ).symm

def glue : SectionRestriction.Sections R M Q F.obj where
  app U := glueAt R M P hP Q J hcover F a ha U.unop.obj U.unop.property
  naturality U V α :=
    (Category.id_comp _).trans
      (glueAt_natural R M P hP Q J hcover F a ha α.unop.hom V.unop.property U.unop.property).symm

theorem glueAt_inside (T : C) (hT : Q T) (i : ι) (hi : P i T) :
    glueAt R M P hP Q J hcover F a ha T hT = (a i).app (op ⟨T, hi⟩) := by
  have h := glueAt_restrict R M P hP Q J hcover F a ha T hT (𝟙 T) ⟨i, hi⟩
  rw [op_id, F.obj.map_id, Category.comp_id] at h
  exact h.trans (CoverFamily.Family.value_eq R M P F.obj a ha T ⟨i, hi⟩ i hi)

theorem glue_restrict (hPQ : ∀ i, P i ≤ Q) (i : ι) :
    SectionRestriction.restrict R M (P i) Q F.obj (hPQ i) (glue R M P hP Q J hcover F a ha) = a i := by
  apply NatTrans.ext
  funext U
  exact glueAt_inside R M P hP Q J hcover F a ha U.unop.obj
    (hPQ i _ U.unop.property) i U.unop.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverGluing
