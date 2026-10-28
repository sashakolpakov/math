import Mathlib
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtIsomorphism

/-! # Zariski Homeomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism

noncomputable section

/-!
# IntegralComparison: Zariski sheaf transport across a homeomorphism in different universes

The opens equivalence preserves the actual point-covering topology.
Consequently its sheaf equivalence applies even when the underlying
space has been lifted into the larger crystalline coefficient universe.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v a b t

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (h : X ≃ₜ Y)

abbrev opensEquiv : Opens X ≌ Opens Y := h.opensCongr.equivalence

instance functor_dense : (opensEquiv h).functor.IsDenseSubsite
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) where
  functorPushforward_mem_iff := by
    intro U S
    constructor
    · intro hS x hx
      have hx' : h x ∈ (opensEquiv h).functor.obj U := by
        change h.symm (h x) ∈ U
        simpa only [h.symm_apply_apply] using hx
      obtain ⟨V, _, ⟨W, c, d, hc, _⟩, hV⟩ := hS (h x) hx'
      refine ⟨W, c, hc, ?_⟩
      have hxW := (leOfHom d) hV
      change h.symm (h x) ∈ W at hxW
      simpa only [h.symm_apply_apply] using hxW
    · intro hS y hy
      change h.symm y ∈ U at hy
      obtain ⟨W, c, hc, hW⟩ := hS (h.symm y) hy
      exact ⟨(opensEquiv h).functor.obj W, (opensEquiv h).functor.map c,
        ⟨W, c, 𝟙 _, hc, rfl⟩, hW⟩

instance inverse_dense : (opensEquiv h).inverse.IsDenseSubsite
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  functor_dense h.symm

def sheafEquiv (A : Type a) [Category.{b} A] :
    Sheaf (Opens.grothendieckTopology X) A ≌ Sheaf (Opens.grothendieckTopology Y) A :=
  (opensEquiv h).sheafCongr _ _ A

variable (A : Type a) [Category.{b} A] [Abelian A]

instance sheafEquiv_additive : (sheafEquiv h A).functor.Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U
    rfl

variable [HasLimitsOfSize.{max u v, max u v} A]
  [HasSheafify (Opens.grothendieckTopology X) A]
  [HasSheafify (Opens.grothendieckTopology Y) A]

def constantTransport (M : A) :
    (sheafEquiv h A).functor.obj ((constantSheaf (Opens.grothendieckTopology X) A).obj M) ≅
      (constantSheaf (Opens.grothendieckTopology Y) A).obj M := by
  letI : ∀ U : (Opens X)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (opensEquiv h).inverse.op) A :=
    fun U => HasLimitsOfShape.of_small.{max u v, max u v} A _
  exact ((opensEquiv h).inverse.pushforwardContinuousSheafificationCompatibility A
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).symm.app
      ((Functor.const _).obj M)

variable [HasExt.{t} (Sheaf (Opens.grothendieckTopology X) A)]
  [HasExt.{t} (Sheaf (Opens.grothendieckTopology Y) A)]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) A)]

def extEquiv (M N : Sheaf (Opens.grothendieckTopology X) A) (n : ℕ) :
    Abelian.Ext.{t} M N n ≃+
      Abelian.Ext.{t} ((sheafEquiv h A).functor.obj M) ((sheafEquiv h A).functor.obj N) n :=
  AddEquiv.ofBijective ((sheafEquiv h A).functor.mapExtAddHom M N n)
    ((sheafEquiv h A).functor.mapExt_bijective_of_preservesInjectiveObjects M N n)

def cohomologyEquiv (M : A) (N : Sheaf (Opens.grothendieckTopology X) A) (n : ℕ) :
    Abelian.Ext.{t} ((constantSheaf (Opens.grothendieckTopology X) A).obj M) N n ≃+
      Abelian.Ext.{t} ((constantSheaf (Opens.grothendieckTopology Y) A).obj M)
        ((sheafEquiv h A).functor.obj N) n :=
  (extEquiv h A ((constantSheaf (Opens.grothendieckTopology X) A).obj M) N n).trans
    (Independent.ExtIsomorphism.sourceEquiv (constantTransport h A M) ((sheafEquiv h A).functor.obj N) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism
