import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

/-! # Cover Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter

noncomputable section

/-! Canonical additive overlap characters of actual sheaf H¹. When every
coefficient section on a connected cover has equal restrictions to its two
overlap projections, the usual overlap difference is independent of all
choices of representatives and local lifts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

universe u
variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
  (hS : S.ShortExact) (U D : X.ProEt) (a b : D ⟶ U)

structure Representative (x : S.X₁.H 1) where
  z : S.X₃.obj.obj (op (⊤_ X.ProEt))
  t : S.X₂.obj.obj (op U)
  c : S.X₁.obj.obj (op D)
  class_eq : Finite.CoverCocycles.connectingSections S hS z = x
  lift_eq : S.g.hom.app (op U) t = S.X₃.obj.map (terminal.from U).op z
  difference_eq : S.f.hom.app (op D) c = S.X₂.obj.map a.op t - S.X₂.obj.map b.op t

include hS

theorem sections_exact (V : X.ProEt) :
    (S.map ((sheafToPresheaf _ Ab.{u + 1}) ⋙ (evaluation _ _).obj (op V))).Exact :=
  ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp
    inferInstance S hS).1

theorem sections_injective (V : X.ProEt) : Function.Injective (S.f.hom.app (op V)) := by
  let : Mono S.f := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

theorem connecting_kernel (z : S.X₃.obj.obj (op (⊤_ X.ProEt)))
    (hz : Finite.CoverCocycles.connectingSections S hS z = 0) :
    ∃ w : S.X₂.obj.obj (op (⊤_ X.ProEt)), S.g.hom.app (op (⊤_ X.ProEt)) w = z := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) hS
    ((Sheaf.H.equiv₀ S.X₃ terminalIsTerminal).symm z) (zero_add 1) hz
  refine ⟨Sheaf.H.equiv₀ S.X₂ terminalIsTerminal y, ?_⟩
  rw [Sheaf.H.equiv₀_naturality]
  exact (congrArg (Sheaf.H.equiv₀ S.X₃ terminalIsTerminal) hy).trans
    (AddEquiv.apply_symm_apply _ _)

variable [Injective S.X₂]
  (hlift : ∀ z : S.X₃.obj.obj (op (⊤_ X.ProEt)),
    ∃ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t =
      S.X₃.obj.map (terminal.from U).op z)

include hlift

theorem representative_exists (x : S.X₁.H 1) :
    Nonempty (Representative S hS U D a b x) := by
  obtain ⟨z, hz⟩ := Finite.CoverCocycles.connectingSections_surjective S hS x
  obtain ⟨t, ht⟩ := hlift z
  have hc : ∃ c : S.X₁.obj.obj (op D),
      S.f.hom.app (op D) c = S.X₂.obj.map a.op t - S.X₂.obj.map b.op t := by
    apply (ShortComplex.ab_exact_iff _).mp (sections_exact S hS D)
    change S.g.hom.app (op D) (S.X₂.obj.map a.op t - S.X₂.obj.map b.op t) = 0
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, ht]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      terminal.comp_from, sub_self]
  obtain ⟨c, hc⟩ := hc
  exact ⟨⟨z, t, c, hz, ht, hc⟩⟩

variable (hcoeff : ∀ v : S.X₁.obj.obj (op U), S.X₁.obj.map a.op v = S.X₁.obj.map b.op v)

include hcoeff

omit [Injective S.X₂] hlift in
theorem representative_unique {x : S.X₁.H 1}
    (r s : Representative S hS U D a b x) : r.c = s.c := by
  have hz : Finite.CoverCocycles.connectingSections S hS (r.z - s.z) = 0 := by
    rw [map_sub, r.class_eq, s.class_eq, sub_self]
  obtain ⟨w, hw⟩ := connecting_kernel S hS (r.z - s.z) hz
  have hker : S.g.hom.app (op U)
      (r.t - s.t - S.X₂.obj.map (terminal.from U).op w) = 0 := by
    rw [map_sub, map_sub, NatTrans.naturality_apply, r.lift_eq, s.lift_eq, hw, map_sub,
      sub_self]
  obtain ⟨v, hv⟩ := (ShortComplex.ab_exact_iff _).mp (sections_exact S hS U) _ hker
  change S.X₁.obj.obj (op U) at v
  change S.f.hom.app (op U) v = r.t - s.t - S.X₂.obj.map (terminal.from U).op w at hv
  have he := congrArg (fun t : S.X₂.obj.obj (op U) =>
    S.X₂.obj.map a.op t - S.X₂.obj.map b.op t) hv
  have hwab : S.X₂.obj.map a.op (S.X₂.obj.map (terminal.from U).op w) =
      S.X₂.obj.map b.op (S.X₂.obj.map (terminal.from U).op w) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      terminal.comp_from]
  have hc : S.X₂.obj.map a.op (S.f.hom.app (op U) v) -
      S.X₂.obj.map b.op (S.f.hom.app (op U) v) = 0 := by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hcoeff v, sub_self]
  rw [hc] at he
  simp only [map_sub, hwab] at he
  apply sections_injective S hS D
  rw [r.difference_eq, s.difference_eq]
  apply sub_eq_zero.mp
  calc
    _ = (S.X₂.obj.map a.op r.t - S.X₂.obj.map a.op s.t -
          S.X₂.obj.map b.op (S.X₂.obj.map (terminal.from U).op w)) -
        (S.X₂.obj.map b.op r.t - S.X₂.obj.map b.op s.t -
          S.X₂.obj.map b.op (S.X₂.obj.map (terminal.from U).op w)) := by abel
    _ = 0 := he.symm

def representative (x : S.X₁.H 1) : Representative S hS U D a b x :=
  Classical.choice (representative_exists S hS U D a b hlift x)

def zeroRepresentative : Representative S hS U D a b 0 where
  z := 0
  t := 0
  c := 0
  class_eq := map_zero _
  lift_eq := by simp
  difference_eq := by simp

def addRepresentative {x y : S.X₁.H 1}
    (r : Representative S hS U D a b x) (s : Representative S hS U D a b y) :
    Representative S hS U D a b (x + y) where
  z := r.z + s.z
  t := r.t + s.t
  c := r.c + s.c
  class_eq := by rw [map_add, r.class_eq, s.class_eq]
  lift_eq := by rw [map_add, r.lift_eq, s.lift_eq, map_add]
  difference_eq := by
    rw [map_add, r.difference_eq, s.difference_eq, map_add, map_add]
    abel

def character : S.X₁.H 1 →+ S.X₁.obj.obj (op D) where
  toFun x := (representative S hS U D a b hlift x).c
  map_zero' := representative_unique S hS U D a b hcoeff
    (representative S hS U D a b hlift 0) (zeroRepresentative S hS U D a b)
  map_add' x y := representative_unique S hS U D a b hcoeff
    (representative S hS U D a b hlift (x + y))
    (addRepresentative S hS U D a b
      (representative S hS U D a b hlift x) (representative S hS U D a b hlift y))

theorem character_cocycle (x : S.X₁.H 1) (T : X.ProEt) (p q r : T ⟶ D)
    (hpa : p ≫ a = r ≫ a) (hpb : p ≫ b = q ≫ a) (hqb : q ≫ b = r ≫ b) :
    S.X₁.obj.map p.op (character S hS U D a b hlift hcoeff x) +
      S.X₁.obj.map q.op (character S hS U D a b hlift hcoeff x) =
        S.X₁.obj.map r.op (character S hS U D a b hlift hcoeff x) := by
  let c := representative S hS U D a b hlift x
  change S.X₁.obj.map p.op c.c + S.X₁.obj.map q.op c.c = S.X₁.obj.map r.op c.c
  apply sections_injective S hS T
  rw [map_add, NatTrans.naturality_apply, NatTrans.naturality_apply,
    NatTrans.naturality_apply, c.difference_eq]
  simp only [map_sub, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    hpa, hpb, hqb]
  abel

variable [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]
  (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left)

include hD in
theorem character_injective : Function.Injective (character S hS U D a b hlift hcoeff) := by
  intro x y hxy
  let r := representative S hS U D a b hlift x
  let s := representative S hS U D a b hlift y
  change r.c = s.c at hxy
  have hcompat : S.X₂.obj.map a.op (r.t - s.t) = S.X₂.obj.map b.op (r.t - s.t) := by
    have he := r.difference_eq.symm.trans ((congrArg (S.f.hom.app (op D)) hxy).trans
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

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter
