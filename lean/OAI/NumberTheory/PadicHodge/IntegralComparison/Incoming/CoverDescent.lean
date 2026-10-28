import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverGluing

/-! # Cover Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverDescent

noncomputable section

/-!
# IntegralComparison: unique descent of sections across incoming full subsites
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverGluing

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) {ι : Type z} (P : ι → ObjectProperty C)
  (hP : ∀ i {U V : C}, (U ⟶ V) → P i V → P i U)
  (Q : ObjectProperty C) (hPQ : ∀ i, P i ≤ Q) (J : GrothendieckTopology C)
  (hcover : ∀ T, Q T → CoverFamily.Family.sieve P hP T ∈ J T)
  (F : Sheaf J (ModuleCat.{w} R))

include hP hcover in
theorem section_ext (b c : SectionRestriction.Sections R M Q F.obj)
    (h : ∀ i, SectionRestriction.restrict R M (P i) Q F.obj (hPQ i) b = SectionRestriction.restrict R M (P i) Q F.obj (hPQ i) c) : b = c := by
  apply NatTrans.ext
  funext T
  apply (F.property M (CoverFamily.Family.sieve P hP T.unop.obj) (hcover T.unop.obj T.unop.property)).isSeparatedFor.ext
  intro U α hα
  obtain ⟨i, hi⟩ := hα
  let UQ : Q.FullSubcategory := ⟨U, hPQ i U hi⟩
  let β : UQ ⟶ T.unop := ObjectProperty.homMk α
  have hb := (b.naturality β.op).symm.trans (Category.id_comp _)
  have hc := (c.naturality β.op).symm.trans (Category.id_comp _)
  have hm := congrArg (fun t : SectionRestriction.Sections R M (P i) F.obj => t.app (op ⟨U, hi⟩)) (h i)
  exact hb.trans (hm.trans hc.symm)

include hcover in
theorem existsUnique (a : ∀ i, SectionRestriction.Sections R M (P i) F.obj) (ha : CoverFamily.Family.Compatible R M P F.obj a) :
    ∃! b : SectionRestriction.Sections R M Q F.obj, ∀ i, SectionRestriction.restrict R M (P i) Q F.obj (hPQ i) b = a i := by
  refine ⟨CoverGluing.glue R M P hP Q J hcover F a ha, CoverGluing.glue_restrict R M P hP Q J hcover F a ha hPQ, ?_⟩
  intro b hb
  apply section_ext R M P hP Q hPQ J hcover F
  intro i
  exact (hb i).trans (CoverGluing.glue_restrict R M P hP Q J hcover F a ha hPQ i).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverDescent
