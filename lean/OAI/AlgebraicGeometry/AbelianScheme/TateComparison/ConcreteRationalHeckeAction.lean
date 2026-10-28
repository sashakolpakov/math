import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralSphericalHom
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalLocalization
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteOrderLocalizationLift
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralHeckeConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralHeckeUnit
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCentralUnit
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteAdditivity

/-! # Concrete Rational Hecke Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The constructed integral Albanese operators extend to the actual
full rational spherical Hecke algebra and its rational Betti action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

def Data.SphericalPELAlbaneseData.integralAlbaneseAction : IntegralSphericalAlgebra.integralSphericalAlgebra s q hElementaryDivisors →ₐ[ℚ] D.EndQ :=
  IntegralSphericalHom.integralSphericalHom s q hElementaryDivisors (fun t => D.toRational (D.heckeEnd hgeometry t))
    (by rw [D.heckeEnd_identity hg hdegree hs hgeometry hIsogenyQuotient, map_one])
    (by
      intro u v
      have hc := congrArg D.toRational (D.heckeEnd_convolution hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors u v)
      refine (D.toRational.map_mul _ _).symm.trans (hc.trans ?_)
      let c : Local.IntegralType s →₀ ℕ := ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v
      let f : D.EndK →+ D.EndQ := D.toRational.toAddMonoidHom
      change f (c.sum (fun w n => n • D.heckeEnd hgeometry w)) =
        c.sum (fun w n => n • f (D.heckeEnd hgeometry w))
      rw [map_finsuppSum]
      simp only [map_nsmul])

theorem Data.SphericalPELAlbaneseData.integralAlbaneseAction_basis (t : Local.IntegralType s) :
    D.integralAlbaneseAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
      ⟨CentralConvolution.sphericalBasis s q t.val, IntegralSphericalAlgebra.integralSphericalSpan_basis s q t⟩ = D.toRational (D.heckeEnd hgeometry t) :=
  IntegralSphericalHom.integralSphericalHom_basis s q hElementaryDivisors _ _ _ t

include hg hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.rationalHeckeAction_exists :
    ∃ ρ : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ,
      ∀ t : Local.IntegralType s, ρ (CentralConvolution.sphericalBasis s q t.val) = D.toRational (D.heckeEnd hgeometry t) := by
  let := SphericalLocalization.sphericalCommRing s q hElementaryDivisors
  let : IsLocalization.Away (SphericalLocalization.integralCentralElement s q hElementaryDivisors) (HeckeKernel.Hecke s q) :=
    SphericalLocalization.spherical_isLocalization s q hElementaryDivisors
  let f := D.integralAlbaneseAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
  obtain ⟨n, hn, hp⟩ := D.centralHeckeEnd_finiteOrder hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
  have he : f (SphericalLocalization.integralCentralElement s q hElementaryDivisors) = D.toRational (D.heckeEnd hgeometry (Local.IntegralType.central s)) :=
    D.integralAlbaneseAction_basis hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors (Local.IntegralType.central s)
  have hf : f (SphericalLocalization.integralCentralElement s q hElementaryDivisors) ^ n = 1 := by
    rw [he, ← map_pow, hp, map_one]
  obtain ⟨ρ, hρ⟩ := FiniteOrderLocalizationLift.exists_algHom_of_finiteOrder_localization (L := HeckeKernel.Hecke s q)
    (SphericalLocalization.integralCentralElement s q hElementaryDivisors) f n (Nat.ne_of_gt hn) hf
  refine ⟨ρ, fun t => ?_⟩
  exact (hρ ⟨CentralConvolution.sphericalBasis s q t.val, IntegralSphericalAlgebra.integralSphericalSpan_basis s q t⟩).trans
    (D.integralAlbaneseAction_basis hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors t)

def Data.SphericalPELAlbaneseData.rationalHeckeAction : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ :=
  (D.rationalHeckeAction_exists hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors).choose

theorem Data.SphericalPELAlbaneseData.rationalHeckeAction_basis (t : Local.IntegralType s) :
    D.rationalHeckeAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors (CentralConvolution.sphericalBasis s q t.val) =
      D.toRational (D.heckeEnd hgeometry t) :=
  (D.rationalHeckeAction_exists hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors).choose_spec t

theorem Data.SphericalPELAlbaneseData.rationalHeckeAction_central_isUnit :
    IsUnit (D.rationalHeckeAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors (CentralConvolution.sphericalBasis s q (Local.LocalType.central s))) := by
  have he := D.rationalHeckeAction_basis hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors (Local.IntegralType.central s)
  exact (congrArg IsUnit he).mpr
    ((D.centralHeckeEnd_isUnit hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors).map D.toRational)

def Data.SphericalPELAlbaneseData.actualSphericalH1Action : HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1 :=
  D.sphericalH1Action (D.pullbackH1Integral_add hgeometry) hElementaryDivisors
    (D.rationalHeckeAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors)

theorem Data.SphericalPELAlbaneseData.actualSphericalH1Action_spec (h : HeckeKernel.Hecke s q) :
    D.IsRationalH1Pullback (D.rationalHeckeAction hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors h)
      (D.actualSphericalH1Action hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors h) :=
  D.sphericalH1Action_spec (D.pullbackH1Integral_add hgeometry) hElementaryDivisors _ h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
