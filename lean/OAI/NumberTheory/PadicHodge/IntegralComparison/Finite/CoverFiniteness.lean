import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.SchemeBaseChange

/-! # Cover Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverFiniteness

noncomputable section

/-! A fixed finite-coefficient acyclic cover makes actual finite-coefficient
H¹ finite when its overlap has finitely many coefficient sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

theorem fiber_nonempty_of_pullback_zero (E : AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n X)
    (U : X.ProEt)
    (h : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 E.extClass = 0) :
    Nonempty (E.Fiber U) := by
  obtain ⟨s, hs⟩ := (E.pullback_eq_zero_iff_lift U.hom).mp h
  exact ⟨E.gluedRepresentative.homEquiv (MorphismProperty.Over.homMk s hs)⟩

theorem presentation_local_lifts
    (I Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (i : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X ⟶ I) (p : I ⟶ Q)
    (hip : i ≫ p = 0) (hS : (ShortComplex.mk i p hip).ShortExact)
    (U : X.ProEt)
    (hzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1,
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 x = 0)
    (z : Q.obj.obj (op (⊤_ X.ProEt))) :
    ∃ t : I.obj.obj (op U), p.hom.app (op U) t =
      Q.obj.map (terminal.from U).op z := by
  let S := ShortComplex.mk i p hip
  obtain ⟨a, ha⟩ := (Ext.mk₀_bijective (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) S.X₃).surjective
    ((Sheaf.H.equiv₀ S.X₃ terminalIsTerminal).symm z)
  let T := AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.pullbackExtensionComplex S a
  let E : AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n X := {
    middle := T.X₂
    inclusion := T.f
    projection := T.g
    zero := T.zero
    shortExact := AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.pullbackExtensionComplex_shortExact hS a }
  obtain ⟨s⟩ := fiber_nonempty_of_pullback_zero ℓ n E U (hzero E.extClass)
  have hgen : a.hom.app (op (⊤_ X.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator X) = z := by
    rw [AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator, Sheaf.H.equiv₀_naturality]
    change Sheaf.H.equiv₀ S.X₃ terminalIsTerminal
      ((Ext.mk₀ (𝟙 _)).comp (Ext.mk₀ a) (add_zero 0)) = z
    rw [Ext.mk₀_id_comp, ha, AddEquiv.apply_symm_apply]
  refine ⟨(pullback.fst S.g a).hom.app (op U) s.val, ?_⟩
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f : (pullback S.g a) ⟶ S.X₃ => f.hom.app (op U))
      (pullback.condition (f := S.g) (g := a))) s.val
  change S.g.hom.app (op U) ((pullback.fst S.g a).hom.app (op U) s.val) =
    a.hom.app (op U) (E.projection.hom.app (op U) s.val) at he
  rw [he, s.property, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator, NatTrans.naturality_apply, hgen]

theorem finite_of_cover
    (U D : X.ProEt) (a b : D ⟶ U)
    [Surjective (terminal.from U).left] [QuasiCompact (terminal.from U).left]
    (hD : IsPullback a.left b.left (terminal.from U).left (terminal.from U).left)
    [Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj (op D))]
    (hzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1,
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 x = 0) :
    Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1) := by
  let F := AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  exact CoverCocycles.finite_of_local_lifts S hS U D a b hD
    (presentation_local_lifts ℓ n S.X₂ S.X₃ S.f S.g S.zero hS U hzero)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverFiniteness
