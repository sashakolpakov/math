import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointSupportLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalModule

/-! # Diagonal Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DiagonalVanishing

noncomputable section

/-! Native local Tor Euler vanishing reduced to the actual support
dimension of the localized external tensor product. The diagonal
comparison, isolated localization, and regular-sequence quotient are
all discharged here. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]

abbrev localRing := Localization.AtPrime (DiagonalSupport.point K R).asIdeal

theorem ideal_proper : (KaehlerDifferential.ideal K R).map (algebraMap (DiagonalTensor.Ring K R) (localRing K R)) ≠ ⊤ := by
  have hI : KaehlerDifferential.ideal K R ≤ (DiagonalSupport.point K R).asIdeal := by
    intro t ht
    change DiagonalTensor.multiplication K R t ∈ IsLocalRing.maximalIdeal R
    change DiagonalTensor.multiplication K R t = 0 at ht
    rw [ht]
    exact (IsLocalRing.maximalIdeal R).zero_mem
  have hm : (KaehlerDifferential.ideal K R).map (algebraMap (DiagonalTensor.Ring K R) (localRing K R)) ≤
      IsLocalRing.maximalIdeal (localRing K R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hI
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (localRing K R)).ne_top hm

theorem euler_zero [IsNoetherianRing R] [IsNoetherianRing (DiagonalTensor.Ring K R)] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) K) R] [IsScalarTower K (MvPolynomial (Fin d) K) R]
    [Algebra.FormallyUnramified (MvPolynomial (Fin d) K) R] [Module.Flat (MvPolynomial (Fin d) K) R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hi : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R})
    (hdim : ∀ p ∈ Module.support (localRing K R)
      ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K R) (localRing K R)).obj (DiagonalTor.external K R M N)),
      ringKrullDim (localRing K R ⧸ p.asIdeal) < d) :
    Tor.Euler.euler R M N d = 0 := by
  let := DiagonalSupport.maximal K R
  let := DiagonalSupport.finite_external K R M N
  let := DiagonalSupport.finite_diagonal K R
  let : Module.Finite (localRing K R)
      ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K R) (localRing K R)).obj (DiagonalTor.external K R M N)) :=
    inferInstanceAs (Module.Finite (localRing K R) (localRing K R ⊗[DiagonalTensor.Ring K R] DiagonalTor.external K R M N))
  have hiso := DiagonalSupport.isolated K R M N hi
  have he := PointSupportLocalization.euler (DiagonalTensor.Ring K R) (DiagonalSupport.point K R)
    (DiagonalTor.external K R M N) (DiagonalTensorNaturality.diagonal K R) hiso d
  have hz := Etale.DiagonalModule.euler_zero K R d (localRing K R) (ideal_proper K R)
    ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K R) (localRing K R)).obj (DiagonalTor.external K R M N)) hdim
    (PointSupportLocalization.isolated (DiagonalTensor.Ring K R) (DiagonalSupport.point K R)
      (DiagonalTor.external K R M N) (DiagonalTensorNaturality.diagonal K R) hiso)
  exact (he.trans (DiagonalTor.euler K R M N d)).symm.trans hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DiagonalVanishing
