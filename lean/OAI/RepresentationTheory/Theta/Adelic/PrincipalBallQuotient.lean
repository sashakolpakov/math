import OAI.RepresentationTheory.Theta.Adelic.PrincipalArchimedeanQuotient
import OAI.RepresentationTheory.Theta.Adelic.GeometricBallProjection
import OAI.RepresentationTheory.Theta.Adelic.BallOrbitQuotient

/-! # Principal Ball Quotient -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalBallQuotient

noncomputable section

/-! Compact Hausdorff second-countable quotients for the exact principal
ball orbit relation appearing in the full AdelicTheta statement. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup OAI.RepresentationTheory.Theta.Adelic.PrincipalArchimedeanQuotient
open OAI.RepresentationTheory.Theta.Adelic.GeometricBallProjection OAI.RepresentationTheory.Theta.Adelic.BallProper OAI.RepresentationTheory.Theta.Adelic.CompactQuotientProjection
open OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

def principalBallGroup : Subgroup BallNatural.BallGroup :=
  ((PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)).map
    (GeometricGroup.geometricBallHom A).toMonoidHom

theorem principalBallGroup_mem_iff (g : BallNatural.BallGroup) :
    g ∈ principalBallGroup A N q hq ↔
      ∃ r : SpecialUnitary.SU H.val, BallGeometryData.PrincipalLevel N r ∧ TensorOrbitSetoid.rationalBallHom A r = g := by
  change g ∈ ((PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)).map
    (GeometricGroup.geometricBallHom A).toMonoidHom ↔ _
  rw [Subgroup.map_map, Subgroup.mem_map]
  simp only [PrincipalSubgroup.principalSubgroup_mem_iff]
  rfl

theorem principal_ball_discrete (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) (hN : 0 < N) :
    DiscreteTopology (principalBallGroup A N q hq) := by
  let : DiscreteTopology ((PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)) :=
    PrincipalArchimedeanQuotient.principal_archimedean_discrete hd hH N hN q hq
  exact NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.discrete_map_of_closedMap (GeometricGroup.geometricBallHom A).toMonoidHom
    (GeometricBallProjection.geometricBallHom_closed A) _

theorem principal_ball_cosets_compact (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) (hN : 0 < N) :
    CompactSpace (BallNatural.BallGroup ⧸ principalBallGroup A N q hq) := by
  let : CompactSpace (RationalSU.ArchimedeanSU F H ⧸
      (PrincipalSubgroup.principalSubgroup F d H N q hq).map (RationalSU.rationalArchimedeanSU F H)) :=
    PrincipalArchimedeanQuotient.principal_archimedean_compact A hd hH N hN q hq
  exact CompactQuotientProjection.compact_cosets_map _ (GeometricGroup.geometricBallHom A).toMonoidHom
    (GeometricGroup.geometricBallHom A).continuous (GeometricBallProjection.geometricBallHom_surjective A)

include q hq in
theorem principal_ball_quotient (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val)
    (hN : 0 < N) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) :
    ∃ R : Setoid BallNatural.Ball, (∀ z w, R.r z w ↔ DataTheta.Descent.BallOrbit (GeometricGaussians.constructedComparison A P) N z w) ∧
      CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) := by
  let Γ := PrincipalSubgroup.principalSubgroup F d H N q hq
  have he : principalBallGroup A N q hq = Γ.map (TensorOrbitSetoid.rationalBallHom A) := by
    exact Subgroup.map_map _ _ _
  let : DiscreteTopology (Γ.map (TensorOrbitSetoid.rationalBallHom A)) :=
    he ▸ principal_ball_discrete A N q hq hd hH hN
  let : CompactSpace (BallNatural.BallGroup ⧸ Γ.map (TensorOrbitSetoid.rationalBallHom A)) :=
    he ▸ principal_ball_cosets_compact A N q hq hd hH hN
  exact BallOrbitQuotient.ballOrbitQuotient_of_compact_discrete A P N Γ
    (PrincipalSubgroup.principalSubgroup_mem_iff F d H N q hq)

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalBallQuotient
