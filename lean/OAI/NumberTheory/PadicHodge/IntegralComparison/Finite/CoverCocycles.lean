import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections

/-! # Cover Cocycles -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

noncomputable section

/-! Finite overlap coefficients bound the actual degree-one sheaf cohomology
when every section in an injective presentation lifts on a fixed cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

universe u

variable {X : Scheme.{u}}

def connectingSections
    (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (hS : S.ShortExact) : S.X₃.obj.obj (op (⊤_ X.ProEt)) →+ S.X₁.H 1 where
  toFun a := ((Sheaf.H.equiv₀ S.X₃ terminalIsTerminal).symm a).comp
    hS.extClass (zero_add 1)
  map_zero' := by simp
  map_add' _ _ := by simp

theorem connectingSections_surjective
    (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (hS : S.ShortExact) [Injective S.X₂] :
    Function.Surjective (connectingSections S hS) := by
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) hS x
    (Ext.eq_zero_of_injective _) rfl
  exact ⟨Sheaf.H.equiv₀ S.X₃ terminalIsTerminal y, by
    simpa only [connectingSections, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddEquiv.symm_apply_apply] using hy⟩

theorem connectingSections_projection
    (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (hS : S.ShortExact) (b : S.X₂.obj.obj (op (⊤_ X.ProEt))) :
    connectingSections S hS (S.g.hom.app (op (⊤_ X.ProEt)) b) = 0 := by
  change ((Sheaf.H.equiv₀ S.X₃ terminalIsTerminal).symm
    (S.g.hom.app (op (⊤_ X.ProEt)) b)).comp hS.extClass (zero_add 1) = 0
  rw [← Sheaf.H.equiv₀_symm_naturality, Sheaf.H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

theorem cover_section_injective (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    {U V : X.ProEt} (f : U ⟶ V) [Surjective f.left] [QuasiCompact f.left] :
    Function.Injective (F.obj.map f.op) := by
  let G := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj F
  have hG : Presieve.IsSheaf (Scheme.ProEt.topology X) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp G.property
  exact Presieve.isSeparatedFor_singleton.mp
    ((hG.isSheafFor (Presieve.singleton f) (AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction.proEtaleSingleton_cover f)).isSeparatedFor)

theorem finite_of_local_lifts
    (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (hS : S.ShortExact) [Injective S.X₂]
    (U D : X.ProEt) (a b : D ⟶ U)
    [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]
    (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left)
    [Finite (S.X₁.obj.obj (op D))]
    (hlift : ∀ z : S.X₃.obj.obj (op (⊤_ X.ProEt)),
      ∃ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t =
        S.X₃.obj.map (terminal.from U).op z) :
    Finite (S.X₁.H 1) := by
  classical
  have hsec : (S.map ((sheafToPresheaf _ Ab.{u + 1}) ⋙
      (evaluation _ _).obj (op D))).Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp
      inferInstance S hS).1
  have hrep (x : S.X₁.H 1) : ∃ z : S.X₃.obj.obj (op (⊤_ X.ProEt)),
      ∃ t : S.X₂.obj.obj (op U), connectingSections S hS z = x ∧
        S.g.hom.app (op U) t = S.X₃.obj.map (terminal.from U).op z := by
    obtain ⟨z, hz⟩ := connectingSections_surjective S hS x
    obtain ⟨t, ht⟩ := hlift z
    exact ⟨z, t, hz, ht⟩
  choose z t hz ht using hrep
  have hc (x : S.X₁.H 1) : ∃ c : S.X₁.obj.obj (op D),
      S.f.hom.app (op D) c = S.X₂.obj.map a.op (t x) - S.X₂.obj.map b.op (t x) := by
    apply (ShortComplex.ab_exact_iff _).mp hsec
    change S.g.hom.app (op D)
      (S.X₂.obj.map a.op (t x) - S.X₂.obj.map b.op (t x)) = 0
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, ht]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      terminal.comp_from, sub_self]
  choose c hc using hc
  apply Finite.of_injective c
  intro x y hxy
  have hcompat : S.X₂.obj.map a.op (t x - t y) = S.X₂.obj.map b.op (t x - t y) := by
    have he := (hc x).symm.trans ((congrArg (S.f.hom.app (op D)) hxy).trans (hc y))
    simp only [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp he
  let F := (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj S.X₂
  obtain ⟨w, hw, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction.proEtaleSheaf_descend_section_of_isPullback F
    (terminal.from U) a b hD (t x - t y) hcompat
  change S.X₂.obj.obj (op (⊤_ X.ProEt)) at w
  change S.X₂.obj.map (terminal.from U).op w = t x - t y at hw
  have hgw : S.g.hom.app (op (⊤_ X.ProEt)) w = z x - z y := by
    apply cover_section_injective S.X₃ (terminal.from U)
    rw [← NatTrans.naturality_apply, hw, map_sub, ht, ht, map_sub]
  have hzero := connectingSections_projection S hS w
  rw [hgw, map_sub, hz, hz] at hzero
  exact sub_eq_zero.mp hzero

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles
