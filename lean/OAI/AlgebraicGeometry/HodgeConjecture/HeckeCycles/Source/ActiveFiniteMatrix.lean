import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledSupport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates

/-! # Active Finite Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveFiniteMatrix.CM

noncomputable section

/-! The actual supported source factor has its prescribed local matrix
and is the identity at every other finite place. Its PEL phase matrix
is therefore supported at the same rational prime. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates.TestTransport

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def active : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →* SourceFinite.Product.CM.FiniteGroup E Q :=
  (SourceFinite.Product.CM.equivalence E Q f).toMonoidHom.comp (MonoidHom.inl _ _)

theorem same (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    active E Q f g (QadicPlace.CM.place E f) =
      (QadicSpecialLinear.CM.equivalence E Q f).symm g :=
  (congrArg (fun u : SourceFinite.Product.CM.FiniteGroup E Q => u (QadicPlace.CM.place E f))
    (mul_one (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (SourceFinite.Product.CM.levels E Q) (QadicPlace.CM.place E f)
      ((QadicSpecialLinear.CM.equivalence E Q f).symm g)))).trans
        (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same _ _ _)

theorem other (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    {v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (QuadraticConjugation.CM.Field.RealField E)}
    (hv : v ≠ QadicPlace.CM.place E f) : active E Q f g v = 1 :=
  (congrArg (fun u : SourceFinite.Product.CM.FiniteGroup E Q => u v)
    (mul_one (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (SourceFinite.Product.CM.levels E Q) (QadicPlace.CM.place E f)
      ((QadicSpecialLinear.CM.equivalence E Q f).symm g)))).trans
        (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other _ hv _)

theorem fill (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    FilledLocal.CM.PEL.fill E Q f (active E Q f g) = 1 := by
  apply RestrictedProduct.ext
  intro v
  by_cases hv : v = QadicPlace.CM.place E f
  · subst v
    exact RestrictedFillComparison.CM.same _ _ _
  · exact (RestrictedFillComparison.CM.other _ _ _ hv).trans (other E Q f g hv)

theorem local_matrix (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    (PELFiniteGroup.CM.equivalence E Q (active E Q f g)).val.val.map
      (CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E f) = g.val :=
  (PELPadic.CM.matrix E Q f (active E Q f g)).trans
    (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] => g.val)
      ((congrArg (QadicSpecialLinear.CM.equivalence E Q f) (same E Q f g)).trans
        ((QadicSpecialLinear.CM.equivalence E Q f).apply_symm_apply g)))

theorem other_local_matrix (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    {p : ℕ} [Fact p.Prime] (τ : E →+* ℚ_[p])
    (hτ : QadicPlace.CM.place E τ ≠ QadicPlace.CM.place E f) :
    (PELFiniteGroup.CM.equivalence E Q (active E Q f g)).val.val.map
      (CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E τ) = 1 :=
  (PELPadic.CM.matrix E Q τ (active E Q f g)).trans
    (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[p] => g.val)
      ((congrArg (QadicSpecialLinear.CM.equivalence E Q τ) (other E Q f g hτ)).trans
        (map_one _)))

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

theorem other_coordinate (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)
    (c : (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
      (c ((PELFiniteGroup.CM.pel E Q P hb (active E Q f g)).val x)) =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (c x) := by
  have h := FilledSupport.CM.other_coordinate E Q P hb f (active E Q f g) x c p hpq
  have he : PELFiniteGroup.CM.pel E Q P hb
      (FilledLocal.CM.PEL.fill E Q f (active E Q f g)) = 1 :=
    (congrArg (PELFiniteGroup.CM.pel E Q P hb) (fill E Q f g)).trans (map_one _)
  have hy : (PELFiniteGroup.CM.pel E Q P hb
      (FilledLocal.CM.PEL.fill E Q f (active E Q f g))).val x = x :=
    (congrArg (fun m : P.FiniteSpecialUnitary => m.val x) he).trans
      (show (1 : P.FiniteSpecialUnitary).val x = x from rfl)
  exact h.symm.trans (congrArg (fun y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (c y)) hy)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveFiniteMatrix.CM
