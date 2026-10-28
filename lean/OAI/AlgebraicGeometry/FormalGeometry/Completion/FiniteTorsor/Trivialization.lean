import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.TorsorSheaf

/-! # Trivialization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: actual local trivializations of finite-coefficient torsors

A local lift translates coefficient sections bijectively to torsor
sections. These bijections commute with restriction, giving a presheaf
isomorphism on the slice over each object with a local lift.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} {X : Scheme.{u}} (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- Translation of a torsor section by an actual coefficient section. -/
def App.Construction.FiniteCoefficientExtension.translate (U : X.ProEt) (a : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op U))
    (s : E.Fiber U) : E.Fiber U :=
  ⟨E.inclusion.hom.app (op U) a + s.val, by
    rw [map_add]
    have h : E.projection.hom.app (op U) (E.inclusion.hom.app (op U) a) = 0 :=
      (E.complex.map ((sheafToPresheaf _ Ab.{u + 1}) ⋙
        (evaluation _ _).obj (op U))).ab_zero_apply a
    rw [h, zero_add, s.property]⟩

theorem App.Construction.FiniteCoefficientExtension.translate_bijective (U : X.ProEt) (s : E.Fiber U) :
    Function.Bijective (fun a => E.translate U a s) := by
  constructor
  · intro a b h
    apply E.inclusion_app_injective U
    exact add_right_cancel (congrArg Subtype.val h)
  · intro t
    obtain ⟨a, ha, _⟩ := E.fiber_unique_difference U s t
    exact ⟨a, Subtype.ext ha⟩

/-- Translation commutes with restriction of both coefficients and torsor sections. -/
theorem App.Construction.FiniteCoefficientExtension.translate_restrict {U V : X.ProEt} (f : V ⟶ U)
    (a : (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op U)) (s : E.Fiber U) :
    E.restrict f (E.translate U a s) =
      E.translate V ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map f.op a) (E.restrict f s) := by
  apply Subtype.ext
  change E.middle.obj.map f.op (E.inclusion.hom.app _ a + s.val) =
    E.inclusion.hom.app _ ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map f.op a) +
      E.middle.obj.map f.op s.val
  simp only [map_add, NatTrans.naturality_apply]

theorem App.Construction.FiniteCoefficientExtension.restrict_comp {U V W : X.ProEt} (f : W ⟶ V) (g : V ⟶ U) (s : E.Fiber U) :
    E.restrict f (E.restrict g s) = E.restrict (f ≫ g) s := by
  apply Subtype.ext
  change E.middle.obj.map f.op (E.middle.obj.map g.op s.val) =
    E.middle.obj.map (f ≫ g).op s.val
  rw [op_comp, Functor.map_comp]
  rfl

/-- A local lift gives a natural map from coefficients to torsor sections on the slice. -/
def App.Construction.FiniteCoefficientExtension.translationOnSlice (U : X.ProEt) (s : E.Fiber U) :
    (Over.forget U).op ⋙ ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj ⋙ forget Ab.{u + 1}) ⟶
      (Over.forget U).op ⋙ E.fiberPresheaf where
  app V := ↾fun a => E.translate V.unop.left a (E.restrict V.unop.hom s)
  naturality V W f := by
    ext a
    change (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op V.unop.left) at a
    change E.translate W.unop.left ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.map f.unop.left.op a)
      (E.restrict W.unop.hom s) =
        E.restrict f.unop.left (E.translate V.unop.left a (E.restrict V.unop.hom s))
    rw [E.translate_restrict, E.restrict_comp, Over.w]

instance App.Construction.FiniteCoefficientExtension.translationOnSlice_isIso (U : X.ProEt) (s : E.Fiber U) :
    IsIso (E.translationOnSlice U s) := by
  have : ∀ V, IsIso ((E.translationOnSlice U s).app V) := fun V =>
    (CategoryTheory.isIso_iff_bijective _).mpr
      (E.translate_bijective V.unop.left (E.restrict V.unop.hom s))
  exact NatIso.isIso_of_isIso_app _

/-- The coefficient presheaf and torsor presheaf are locally isomorphic. -/
def App.Construction.FiniteCoefficientExtension.trivialization (U : X.ProEt) (s : E.Fiber U) :
    (Over.forget U).op ⋙ ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj ⋙ forget Ab.{u + 1}) ≅
      (Over.forget U).op ⋙ E.fiberPresheaf :=
  asIso (E.translationOnSlice U s)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
