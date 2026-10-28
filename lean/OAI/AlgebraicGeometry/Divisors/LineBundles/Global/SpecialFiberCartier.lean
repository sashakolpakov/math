import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberPrincipalKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.ImmersionCodimension

/-! # Special Fiber Cartier -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberCartier.BundleCycles

noncomputable section

/-! On an integral ambient scheme the actual deformation parameter is regular, so its scheme-theoretic special fiber is an effective Cartier divisor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme.{0}} [IsIntegral X] (I : X.IdealSheafData)

theorem globalSpecialFiber_regularPrincipalImageIdeals :
    Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (SpecialFiber.BundleCycles.globalSpecialFiberMap I) := by
  intro x
  obtain ⟨U, hU, hxU, hk⟩ := SpecialFiberPrincipalKernel.BundleCycles.globalSpecialFiber_exists_principal_affineNeighborhood I x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let sU := (Deformation.BundleCycles.globalDeformation I).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (Specialization.BundleCycles.globalDeformationParameterSection I)
  have hs : sU ≠ 0 := (map_ne_zero_iff _
    (map_injective_of_isIntegral (Deformation.BundleCycles.globalDeformation I) (homOfLE (show U ≤ ⊤ from le_top)))).mpr
      (Specialization.BundleCycles.globalDeformationParameterSection_ne_zero I)
  exact ⟨⟨U, hU⟩, hxU, sU, isRegular_iff_ne_zero.mpr hs, hk⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberCartier.BundleCycles
