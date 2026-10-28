import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Matrix Rational Determination -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixRationalDetermination.CM

noncomputable section

/-! A finite-adele matrix is determined by its action on rational
vectors. This identifies representations after a proved rational frame. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ext (A B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (h : ∀ x : I → ℚ, A *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x = B *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) : A = B := by
  have hc (M : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Continuous (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => M *ᵥ x) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => ∑ j, M i j * x j)
    fun_prop
  have he : (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => A *ᵥ x) = (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => B *ᵥ x) :=
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.denseRange_finiteDiagonal.equalizer (hc A) (hc B) (funext h)
  apply Matrix.toLin'.injective
  exact LinearMap.ext (congrFun he)

theorem eq_map (A : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (B : Matrix I I ℚ)
    (h : ∀ x : I → ℚ, A *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (B *ᵥ x)) :
    A = B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := by
  apply CM.ext
  intro x
  refine (h x).trans ?_
  funext i
  exact RingHom.map_mulVec (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) B x i

theorem eq_map_of_frame {V : Type*} (e : V → (I → ℚ)) (he : Function.Surjective e)
    (u : V → V) (A : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (B : Matrix I I ℚ)
    (hA : ∀ x, A *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (e x) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (e (u x)))
    (hB : ∀ x, B *ᵥ e x = e (u x)) : A = B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := by
  apply eq_map
  intro y
  obtain ⟨x, rfl⟩ := he y
  exact (hA x).trans (congrArg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (hB x)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixRationalDetermination.CM
