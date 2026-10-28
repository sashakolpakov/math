import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Rosati Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The Rosati conjugation condition is preserved by actual scheme
base change, including its normalized Poincare pullback identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

theorem RosatiBaseChange.poincareEndomorphism_baseChange {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (u : D.abelian.scheme ⟶ D.abelian.scheme)
    (v : A.scheme ⟶ A.scheme) (f : S' ⟶ S) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (((Over.pullback f).map u) ⊗ₘ ((Over.pullback f).map v)).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback f).poincare) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap f).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ⊗ₘ v).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) :=
  (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
    (((Over.pullback f).map u) ⊗ₘ ((Over.pullback f).map v)).left
    (D.poincarePullbackOverMap f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
      ((congrArg (fun h => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
        (HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality D D u v f)).trans
          (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (D.poincarePullbackOverMap f).left
            (u ⊗ₘ v).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)))

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ActionData.RosatiConjugation.pullback (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (f : S' ⟶ S) :
    ActionData.RosatiConjugation (A.pullback f) (ρ.pullback f) := by
  intro a
  obtain ⟨u, hu, hp, ha⟩ := hρ a
  let : IsMonHom u := hu
  refine ⟨(Over.pullback f).map u, inferInstanceAs (IsMonHom ((Over.pullback f).map u)), ?_, ?_⟩
  · have h₁ := RosatiBaseChange.poincareEndomorphism_baseChange A.dual u (𝟙 A.abelian.scheme) f
    have h₂ := RosatiBaseChange.poincareEndomorphism_baseChange A.dual (𝟙 A.dual.abelian.scheme) (ρ.map a) f
    rw [(Over.pullback f).map_id] at h₁ h₂
    exact h₁.trans ((congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) hp).trans h₂.symm)
  · exact ((Over.pullback f).map_comp A.polarization.isogeny.hom u).symm.trans
      ((congrArg (fun h => (Over.pullback f).map h) ha).trans
        ((Over.pullback f).map_comp (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
          A.polarization.isogeny.hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
