import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneTransport

/-! # Complex Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexMap.HodgeComplexMap

noncomputable section

/-! Functoriality of the original Hodge truncation and its preservation of low-degree derived equivalences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ}

def map (f : K ⟶ L) (r : ℤ) : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ⟶ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r :=
  TruncatedFunctorIso.TruncatedPullback.map (𝟭 C) f r

theorem inclusion (f : K ⟶ L) (r : ℤ) :
    map f r ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ f :=
  TruncatedFunctorIso.TruncatedPullback.inclusion_square (𝟭 C) f r

theorem component_isIso (f : K ⟶ L) (r : ℤ) (n : ℕ) [IsIso (f.f n)] : IsIso ((map f r).f n) := by
  by_cases h : r ≤ (n : ℤ)
  · let e : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n :=
      eqToIso (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n = K.X n from ite_eq_left h) ≪≫ asIso (f.f n) ≪≫
        eqToIso (show L.X n = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n from (ite_eq_left h).symm)
    change IsIso (TruncatedFunctorIso.TruncatedPullback.component (𝟭 C) f r n)
    dsimp only [TruncatedFunctorIso.TruncatedPullback.component]
    rw [dite_eq_left h]
    exact e.isIso_hom
  · have hK : IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n) := by
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right h]
      exact isZero_zero C
    have hL : IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n) := by
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right h]
      exact isZero_zero C
    exact hK.isIso hL _

variable [HasDerivedCategory.{w} C]

theorem hone_bijective (A : C) (f : K ⟶ L)
    (h : ∀ n : ℕ, n ≤ 2 → IsIso (f.f n)) (r : ℤ) :
    Function.Bijective (FirstThree.OneTransport.FirstThreeHOneTransport.map A (map f r)) := by
  apply FirstThree.OneTransport.FirstThreeHOneTransport.bijective
  intro n hn
  let : IsIso (f.f n) := h n hn
  exact component_isIso f r n

theorem projection_hone_bijective (A : C) (K : CochainComplex C ℕ) (r : ℤ) :
    Function.Bijective (FirstThree.OneTransport.FirstThreeHOneTransport.map A (map (FirstThree.ThreeComplex.FirstThreeComplex.projection K) r)) := by
  apply hone_bijective
  intro n hn
  rcases n with _ | (_ | (_ | n))
  · exact inferInstanceAs (IsIso (𝟙 (K.X 0)))
  · exact inferInstanceAs (IsIso (𝟙 (K.X 1)))
  · exact inferInstanceAs (IsIso (𝟙 (K.X 2)))
  · omega

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexMap.HodgeComplexMap
