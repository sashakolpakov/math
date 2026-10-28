import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSingleCoverCocycles

/-! # Cover Cocycle Surjectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleSurjectivity

noncomputable section

/-! Actual overlap cocycles give degree-one sheaf cohomology classes.
The construction takes a primitive in an injective sheaf, descends its
quotient section, and applies the connecting homomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

universe u
variable {X : Scheme.{u}} (U D : X.ProEt) (a b : D ⟶ U)
  [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]
  (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left)

theorem coveringObjects (V : X.ProEt) :
    CoveringObjectsSheafDetection.sieve (fun _ : PUnit.{u + 1} => U) V ∈
      Scheme.ProEt.topology X V := by
  apply (Scheme.ProEt.topology X).superset_covering ?_
    ((Scheme.ProEt.topology X).pullback_stable (terminal.from V)
      (AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction.proEtaleSingleton_cover (terminal.from U)))
  rintro W f ⟨Z, g, h, hh, he⟩
  cases hh
  exact ⟨PUnit.unit, ⟨g⟩⟩

include hD in
omit [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left] in
theorem sitePullback : IsPullback a b (terminal.from U) (terminal.from U) := by
  exact IsPullback.of_map ((Scheme.ProEt.forget X) ⋙ Over.forget X) (by simp) hD

variable
  (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
  (hS : S.ShortExact) [Injective S.X₂]
  (hlift : ∀ z : S.X₃.obj.obj (op (⊤_ X.ProEt)),
    ∃ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t =
      S.X₃.obj.map (terminal.from U).op z)
  (hcoeff : ∀ v : S.X₁.obj.obj (op U), S.X₁.obj.map a.op v = S.X₁.obj.map b.op v)

include hD in
theorem exists_class (c : S.X₁.obj.obj (op D))
    (hc : ∀ (T : X.ProEt) (p q r : T ⟶ D), p ≫ a = r ≫ a → p ≫ b = q ≫ a →
      q ≫ b = r ≫ b → S.X₁.obj.map p.op c + S.X₁.obj.map q.op c = S.X₁.obj.map r.op c) :
    ∃ x : S.X₁.H 1, CoverCharacter.character S hS U D a b hlift hcoeff x = c := by
  have hc' : ∀ (T : X.ProEt) (p q r : T ⟶ D), p ≫ a = r ≫ a → p ≫ b = q ≫ a →
      q ≫ b = r ≫ b →
      S.X₂.obj.map p.op (S.f.hom.app (op D) c) + S.X₂.obj.map q.op (S.f.hom.app (op D) c) =
        S.X₂.obj.map r.op (S.f.hom.app (op D) c) := by
    intro T p q r hpa hpb hqb
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
      ← NatTrans.naturality_apply, ← map_add, hc T p q r hpa hpb hqb]
  obtain ⟨t, ht⟩ := InjectiveSingleCoverCocycles.primitive.{u + 1, u}
    (Scheme.ProEt.topology X) S.X₂ U D a b (sitePullback U D a b hD)
    (coveringObjects U) (S.f.hom.app (op D) c) hc'
  have hzero : S.g.hom.app (op D) (S.f.hom.app (op D) c) = 0 := by
    have he := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom.app (op D) c) S.zero
    exact he
  have hcompat : S.X₃.obj.map a.op (S.g.hom.app (op U) t) =
      S.X₃.obj.map b.op (S.g.hom.app (op U) t) := by
    apply sub_eq_zero.mp
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← map_sub, ht, hzero]
  let F := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj S.X₃
  obtain ⟨z, hz, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback F
    (terminal.from U) a b hD (S.g.hom.app (op U) t) hcompat
  change S.X₃.obj.obj (op (⊤_ X.ProEt)) at z
  change S.X₃.obj.map (terminal.from U).op z = S.g.hom.app (op U) t at hz
  let x := Finite.CoverCocycles.connectingSections S hS z
  let r : CoverCharacter.Representative S hS U D a b x :=
    ⟨z, t, c, rfl, hz.symm, ht.symm⟩
  exact ⟨x, CoverCharacter.representative_unique S hS U D a b hcoeff
    (CoverCharacter.representative S hS U D a b hlift x) r⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleSurjectivity
