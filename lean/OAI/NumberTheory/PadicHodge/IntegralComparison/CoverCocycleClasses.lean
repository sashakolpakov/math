import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleSurjectivity

/-! # Cover Cocycle Classes -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleClasses

noncomputable section

/-! A cocycle on a genuine pro-étale cover determines a sheaf H¹ class,
without a connectedness assumption on that cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

universe u
variable {X : Scheme.{u}} (U D : X.ProEt) (a b : D ⟶ U)
  [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]
  (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left)
  (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) (hS : S.ShortExact)

include hD in
theorem class_eq_of_cocycle_eq {x y : S.X₁.H 1}
    (r : CoverCharacter.Representative S hS U D a b x) (s : CoverCharacter.Representative S hS U D a b y)
    (hrs : r.c = s.c) : x = y := by
  have hcompat : S.X₂.obj.map a.op (r.t - s.t) = S.X₂.obj.map b.op (r.t - s.t) := by
    have he := r.difference_eq.symm.trans ((congrArg (S.f.hom.app (op D)) hrs).trans
      s.difference_eq)
    simp only [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp he
  let F := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj S.X₂
  obtain ⟨w, hw, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback F
    (terminal.from U) a b hD (r.t - s.t) hcompat
  change S.X₂.obj.obj (op (⊤_ X.ProEt)) at w
  change S.X₂.obj.map (terminal.from U).op w = r.t - s.t at hw
  have hgw : S.g.hom.app (op (⊤_ X.ProEt)) w = r.z - s.z := by
    apply Finite.CoverCocycles.cover_section_injective S.X₃ (terminal.from U)
    rw [← NatTrans.naturality_apply, hw, map_sub, r.lift_eq, s.lift_eq, map_sub]
  have hzero := Finite.CoverCocycles.connectingSections_projection S hS w
  rw [hgw, map_sub, r.class_eq, s.class_eq] at hzero
  exact sub_eq_zero.mp hzero

variable [Injective S.X₂]

include hD in
theorem exists_representative (c : S.X₁.obj.obj (op D))
    (hc : ∀ (T : X.ProEt) (p q r : T ⟶ D), p ≫ a = r ≫ a → p ≫ b = q ≫ a →
      q ≫ b = r ≫ b → S.X₁.obj.map p.op c + S.X₁.obj.map q.op c = S.X₁.obj.map r.op c) :
    ∃ x : S.X₁.H 1, ∃ r : CoverCharacter.Representative S hS U D a b x, r.c = c := by
  have hc' : ∀ (T : X.ProEt) (p q r : T ⟶ D), p ≫ a = r ≫ a → p ≫ b = q ≫ a →
      q ≫ b = r ≫ b →
      S.X₂.obj.map p.op (S.f.hom.app (op D) c) + S.X₂.obj.map q.op (S.f.hom.app (op D) c) =
        S.X₂.obj.map r.op (S.f.hom.app (op D) c) := by
    intro T p q r hpa hpb hqb
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
      ← NatTrans.naturality_apply, ← map_add, hc T p q r hpa hpb hqb]
  obtain ⟨t, ht⟩ := InjectiveSingleCoverCocycles.primitive.{u + 1, u}
    (Scheme.ProEt.topology X) S.X₂ U D a b
    (CoverCocycleSurjectivity.sitePullback U D a b hD)
    (CoverCocycleSurjectivity.coveringObjects U) (S.f.hom.app (op D) c) hc'
  have hzero : S.g.hom.app (op D) (S.f.hom.app (op D) c) = 0 :=
    congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom.app (op D) c) S.zero
  have hcompat : S.X₃.obj.map a.op (S.g.hom.app (op U) t) =
      S.X₃.obj.map b.op (S.g.hom.app (op U) t) := by
    apply sub_eq_zero.mp
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← map_sub, ht, hzero]
  let F := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj S.X₃
  obtain ⟨z, hz, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback F
    (terminal.from U) a b hD (S.g.hom.app (op U) t) hcompat
  change S.X₃.obj.obj (op (⊤_ X.ProEt)) at z
  change S.X₃.obj.map (terminal.from U).op z = S.g.hom.app (op U) t at hz
  exact ⟨Finite.CoverCocycles.connectingSections S hS z, ⟨z, t, c, rfl, hz.symm, ht.symm⟩, rfl⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleClasses
