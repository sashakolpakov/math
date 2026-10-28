import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter

/-! # Cover Character Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality

noncomputable section

/-! The actual H¹ overlap character is natural for coefficient maps
and refinements of covers. The proof transports genuine representatives
through a morphism of short exact sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

universe u
variable {X : Scheme.{u}}
  {S T : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})}
  (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)

theorem connecting_naturality (z : S.X₃.obj.obj (op (⊤_ X.ProEt))) :
    Finite.CoverCocycles.connectingSections T hT (φ.τ₃.hom.app (op (⊤_ X.ProEt)) z) =
      Sheaf.H.map φ.τ₁ 1 (Finite.CoverCocycles.connectingSections S hS z) := by
  change ((Sheaf.H.equiv₀ T.X₃ terminalIsTerminal).symm
      (φ.τ₃.hom.app (op (⊤_ X.ProEt)) z)).comp hT.extClass (zero_add 1) =
    Sheaf.H.map φ.τ₁ 1
      (((Sheaf.H.equiv₀ S.X₃ terminalIsTerminal).symm z).comp hS.extClass (zero_add 1))
  rw [← Sheaf.H.equiv₀_symm_naturality, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    hS.extClass_naturality hT φ]

theorem app_comm₁₂ (V : X.ProEt) (x : S.X₁.obj.obj (op V)) :
    T.f.hom.app (op V) (φ.τ₁.hom.app (op V) x) =
      φ.τ₂.hom.app (op V) (S.f.hom.app (op V) x) :=
  congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom.app (op V) x) φ.comm₁₂

theorem app_comm₂₃ (V : X.ProEt) (x : S.X₂.obj.obj (op V)) :
    T.g.hom.app (op V) (φ.τ₂.hom.app (op V) x) =
      φ.τ₃.hom.app (op V) (S.g.hom.app (op V) x) :=
  congrArg (fun f : S.X₂ ⟶ T.X₃ => f.hom.app (op V) x) φ.comm₂₃

theorem restriction_comp (H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    {V W Z : X.ProEt} (f : V ⟶ W) (g : W ⟶ Z) (x : H.obj.obj (op Z)) :
    H.obj.map f.op (H.obj.map g.op x) = H.obj.map (f ≫ g).op x := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

variable (U D V E : X.ProEt) (a b : D ⟶ U) (c d : E ⟶ V)
  (rU : V ⟶ U) (rD : E ⟶ D) (ha : rD ≫ a = c ≫ rU) (hb : rD ≫ b = d ≫ rU)

def mapRepresentative {x : S.X₁.H 1} (r : CoverCharacter.Representative S hS U D a b x) :
    CoverCharacter.Representative T hT V E c d (Sheaf.H.map φ.τ₁ 1 x) where
  z := φ.τ₃.hom.app (op (⊤_ X.ProEt)) r.z
  t := φ.τ₂.hom.app (op V) (S.X₂.obj.map rU.op r.t)
  c := φ.τ₁.hom.app (op E) (S.X₁.obj.map rD.op r.c)
  class_eq := (connecting_naturality hS hT φ r.z).trans (congrArg (Sheaf.H.map φ.τ₁ 1) r.class_eq)
  lift_eq := by
    rw [app_comm₂₃, NatTrans.naturality_apply, r.lift_eq]
    rw [restriction_comp, terminal.comp_from, NatTrans.naturality_apply]
  difference_eq := by
    rw [app_comm₁₂, NatTrans.naturality_apply, r.difference_eq, map_sub, map_sub]
    rw [restriction_comp, restriction_comp, ha, hb,
      ← restriction_comp S.X₂ c rU, ← restriction_comp S.X₂ d rU]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    simp only [NatTrans.naturality_apply]

variable [Injective S.X₂] [Injective T.X₂]
  (hSlift : ∀ z : S.X₃.obj.obj (op (⊤_ X.ProEt)),
    ∃ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t = S.X₃.obj.map (terminal.from U).op z)
  (hTlift : ∀ z : T.X₃.obj.obj (op (⊤_ X.ProEt)),
    ∃ t : T.X₂.obj.obj (op V), T.g.hom.app (op V) t = T.X₃.obj.map (terminal.from V).op z)
  (hScoeff : ∀ z : S.X₁.obj.obj (op U), S.X₁.obj.map a.op z = S.X₁.obj.map b.op z)
  (hTcoeff : ∀ z : T.X₁.obj.obj (op V), T.X₁.obj.map c.op z = T.X₁.obj.map d.op z)

include ha hb in
theorem character_naturality (x : S.X₁.H 1) :
    CoverCharacter.character T hT V E c d hTlift hTcoeff (Sheaf.H.map φ.τ₁ 1 x) =
      φ.τ₁.hom.app (op E) (S.X₁.obj.map rD.op (CoverCharacter.character S hS U D a b hSlift hScoeff x)) := by
  exact CoverCharacter.representative_unique T hT V E c d hTcoeff
    (CoverCharacter.representative T hT V E c d hTlift _)
    (mapRepresentative hS hT φ U D V E a b c d rU rD ha hb
      (CoverCharacter.representative S hS U D a b hSlift x))

theorem character_refinement_square
    (sU : U ⟶ V) (sD : D ⟶ E) (hc : sD ≫ c = a ≫ sU) (hd : sD ≫ d = b ≫ sU)
    (hTcoeffU : ∀ z : T.X₁.obj.obj (op U), T.X₁.obj.map a.op z = T.X₁.obj.map b.op z)
    (x : S.X₁.H 1) :
    φ.τ₁.hom.app (op D) (CoverCharacter.character S hS U D a b hSlift hScoeff x) =
      T.X₁.obj.map sD.op
        (CoverCharacter.character T hT V E c d hTlift hTcoeff (Sheaf.H.map φ.τ₁ 1 x)) := by
  let r := mapRepresentative hS hT φ U D U D a b a b (𝟙 U) (𝟙 D)
    (by simp) (by simp) (CoverCharacter.representative S hS U D a b hSlift x)
  let s := mapRepresentative hT hT (𝟙 T) V E U D c d a b sU sD hc hd
    (CoverCharacter.representative T hT V E c d hTlift (Sheaf.H.map φ.τ₁ 1 x))
  let s' : CoverCharacter.Representative T hT U D a b (Sheaf.H.map φ.τ₁ 1 x) := {
    z := s.z, t := s.t, c := s.c
    class_eq := s.class_eq.trans (Sheaf.H.map_id_apply _)
    lift_eq := s.lift_eq, difference_eq := s.difference_eq }
  have he := CoverCharacter.representative_unique T hT U D a b hTcoeffU r s'
  change φ.τ₁.hom.app (op D)
      (S.X₁.obj.map (𝟙 D).op (CoverCharacter.character S hS U D a b hSlift hScoeff x)) =
    (𝟙 T.X₁ : T.X₁ ⟶ T.X₁).hom.app (op D)
      (T.X₁.obj.map sD.op
        (CoverCharacter.character T hT V E c d hTlift hTcoeff (Sheaf.H.map φ.τ₁ 1 x))) at he
  have hi : (𝟙 T.X₁ : T.X₁ ⟶ T.X₁).hom.app (op D) = 𝟙 (T.X₁.obj.obj (op D)) := rfl
  rw [hi] at he
  simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality
