import OAI.RepresentationTheory.Theta.Adelic.PrincipalBallQuotient
import OAI.RepresentationTheory.Theta.Adelic.PrincipalFiniteCofinal
import OAI.RepresentationTheory.Theta.Adelic.PrincipalTorsion
import OAI.RepresentationTheory.Theta.Adelic.TensorSectionDescent
import OAI.RepresentationTheory.Theta.Adelic.Data

/-! # Congruence Descent -/

namespace OAI.RepresentationTheory.Theta.Adelic.CongruenceDescent

noncomputable section

/-! The full congruence-descent conclusion: cofinal literal principal
levels, torsion-freeness, compact ball quotients, and continuous sections
of the actual symmetric geometric tensor bundles. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.Data
open OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup OAI.RepresentationTheory.Theta.Adelic.PrincipalDenominator OAI.RepresentationTheory.Theta.Adelic.PrincipalFiniteCofinal
open OAI.RepresentationTheory.Theta.Adelic.PrincipalTorsion OAI.RepresentationTheory.Theta.Adelic.PrincipalBallQuotient OAI.RepresentationTheory.Theta.Adelic.TensorSectionDescent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem constructedComparison_congruence (hH : H.val.conjTranspose = H.val)
    (hfinite : Data.FiniteConclusion F d 3 m H K hd C P D)
    (hΘ : DataTheta.Descent.ThetaConstruction (GeometricGaussians.constructedComparison A P))
    (hHecke : DataTheta.Descent.RationalHeckeCovariance (GeometricGaussians.constructedComparison A P) P hd C D) :
    DataTheta.Descent.CongruenceDescent (GeometricGaussians.constructedComparison A P) P hd C D := by
  intro Φ K₀ N₀ hN₀
  obtain ⟨L, hLc, hLK, hfix⟩ := hfinite.2 Φ K₀
  obtain ⟨c, hc, hcofinal⟩ := PrincipalFiniteCofinal.principal_finite_cofinal F H L
  obtain ⟨t, ht, q, hq⟩ := PrincipalDenominator.exists_positive_integral_multiple F d
  let N := N₀ * (3 * t * c)
  have hN : 0 < N := Nat.mul_pos hN₀ (Nat.mul_pos (Nat.mul_pos (by decide) ht) hc)
  have hN₀N : N₀ ∣ N := dvd_mul_right N₀ (3 * t * c)
  have h3t : 3 * t ∣ N := ⟨N₀ * c, by dsimp [N]; ring⟩
  have hcN : c ∣ N := ⟨N₀ * (3 * t), by dsimp [N]; ring⟩
  have htN : t ∣ N := dvd_trans (dvd_mul_left t 3) h3t
  obtain ⟨qN, hqN⟩ := PrincipalDenominator.integral_multiple_of_dvd F d t N q hq htN
  obtain ⟨R, hR, hRc, hRt, hRs⟩ := PrincipalBallQuotient.principal_ball_quotient A N qN hqN hd hH hN P
  refine ⟨N, hN, hN₀N, PrincipalTorsion.principalLevel_torsion_free F d H t q hq N h3t,
    L, hLc, hLK, hcofinal N hcN, hfix, R, hR, hRc, hRt, hRs, ?_⟩
  intro a
  exact TensorSectionDescent.tensor_sections_of_fixed_principal_level A P hd C D hΘ hHecke N
    (PrincipalSubgroup.principalSubgroup F d H N qN hqN) (PrincipalSubgroup.principalSubgroup_mem_iff F d H N qN hqN)
    Φ (fun f hf g hg => hfix f hf _ (hcofinal N hcN g hg)) R hR a

end

end OAI.RepresentationTheory.Theta.Adelic.CongruenceDescent
