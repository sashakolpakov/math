import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates

/-! # Norm One Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM

noncomputable section

/-! Rational norm-one multiplication in the original source coordinates.
The resulting symplectic matrix is the literal scalar matrix used by
RadialDilation, and its complex action is multiplication at every CM embedding. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)

include hr in
theorem hermitian_preserved (x y : GeometricSource.CM.Vec E) :
    GeometricSource.CM.hermitian E B.b (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.rationalScalarEnd E (r : E) x) (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.rationalScalarEnd E (r : E) y) =
      GeometricSource.CM.hermitian E B.b x y := by
  unfold GeometricSource.CM.hermitian
  apply Finset.sum_congr rfl
  intro j _
  change (if j = 2 then B.b else 1) * ((r : E) * x j) *
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E ((r : E) * y j) = _
  rw [map_mul]
  calc
    _ = ((r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E)) *
        ((if j = 2 then B.b else 1) * x j * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (y j)) := by ring
    _ = _ := by rw [hr, one_mul]

def scalar : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ :=
  ⟨RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E (ComplexAction.CM.Symplectic.frame E C) (r : E), by
    apply ComplexAction.CM.Symplectic.matrix_symplectic
    intro x y
    obtain ⟨x, rfl⟩ := (ComplexAction.CM.Symplectic.frame E C).surjective x
    obtain ⟨y, rfl⟩ := (ComplexAction.CM.Symplectic.frame E C).surjective y
    rw [RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix_apply, RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix_apply, ComplexAction.CM.Symplectic.frame_pairing,
      ComplexAction.CM.Symplectic.frame_pairing, hermitian_preserved E r hr]⟩

theorem matrix_eq : (scalar E C r hr).val = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E (ComplexAction.CM.Symplectic.frame E C) (r : E) := rfl

theorem scalar_apply (x : GeometricSource.CM.Vec E) :
    (scalar E C r hr).val.mulVec (ComplexAction.CM.Symplectic.frame E C x) = ComplexAction.CM.Symplectic.frame E C (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.rationalScalarEnd E (r : E) x) :=
  RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix_apply E (ComplexAction.CM.Symplectic.frame E C) (r : E) x

def ambient : Module.End ℂ (GeometricSource.CM.Ambient E) :=
  LinearMap.pi (fun τ : Gal(E/ℚ) => ((τ (r : E) : E) : ℂ) • LinearMap.proj τ)

omit [NumberField E] [NumberField.IsCMField E] in
theorem ambient_apply (x : GeometricSource.CM.Ambient E) (τ : Gal(E/ℚ)) (j : Fin 3) :
    ambient E r x τ j = ((τ (r : E) : E) : ℂ) * x τ j := rfl

omit [NumberField E] [NumberField.IsCMField E] in
theorem ambient_rational (x : GeometricSource.CM.Vec E) :
    ambient E r (GeometricSource.CM.embeddingCoordinates E x) = GeometricSource.CM.embeddingCoordinates E (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.rationalScalarEnd E (r : E) x) := by
  ext τ j
  simp only [ambient_apply, GeometricSource.CM.embeddingCoordinates, RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.rationalScalarEnd, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul, IntermediateField.coe_mul]

theorem rational_matrix_frame (x : GeometricSource.CM.Vec E) :
    ((scalar E C r hr).val.map (algebraMap ℚ ℂ)).mulVec
        (ComplexAction.CM.complexFrame E C (GeometricSource.CM.embeddingCoordinates E x)) =
      ComplexAction.CM.complexFrame E C (ambient E r (GeometricSource.CM.embeddingCoordinates E x)) := by
  rw [ComplexAction.CM.complexFrame_rational, ambient_rational, ComplexAction.CM.complexFrame_rational]
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (scalar E C r hr).val (ComplexAction.CM.Symplectic.frame E C x) i).symm.trans
    (congrArg (algebraMap ℚ ℂ) (congrFun (scalar_apply E C r hr x) i))

theorem complex_matrix_frame (x : GeometricSource.CM.Ambient E) :
    ((scalar E C r hr).val.map (algebraMap ℚ ℂ)).mulVec (ComplexAction.CM.complexFrame E C x) =
      ComplexAction.CM.complexFrame E C (ambient E r x) := by
  let T := Matrix.toLin' ((scalar E C r hr).val.map (algebraMap ℚ ℂ))
  let U := (ComplexAction.CM.complexFrame E C).toLinearMap.comp
    ((ambient E r).comp (ComplexAction.CM.complexFrame E C).symm.toLinearMap)
  have hTU : T = U := by
    apply (Pi.basisFun ℂ (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places)).ext
    intro i
    have hs : (Pi.single i (1 : ℂ) : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ) =
        fun k => ((Pi.single i (1 : ℚ) : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) k : ℂ) := by
      funext k
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    simp only [Pi.basisFun_apply]
    rw [hs]
    change ((scalar E C r hr).val.map (algebraMap ℚ ℂ)).mulVec _ =
      ComplexAction.CM.complexFrame E C (ambient E r ((ComplexAction.CM.complexFrame E C).symm _))
    rw [ComplexAction.CM.complexFrame_symm_rational]
    simpa only [ComplexAction.CM.complexFrame_rational, LinearEquiv.apply_symm_apply] using
      rational_matrix_frame E C r hr ((ComplexAction.CM.Symplectic.frame E C).symm (Pi.single i 1))
  have h := LinearMap.congr_fun hTU (ComplexAction.CM.complexFrame E C x)
  change _ = ComplexAction.CM.complexFrame E C (ambient E r ((ComplexAction.CM.complexFrame E C).symm (ComplexAction.CM.complexFrame E C x))) at h
  rwa [LinearEquiv.symm_apply_apply] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM
