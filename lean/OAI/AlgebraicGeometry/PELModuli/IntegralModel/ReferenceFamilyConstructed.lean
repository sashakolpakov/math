import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamily
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Components

/-! # Reference Family Constructed -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamilyConstructed

noncomputable section

/-! The ReferenceFamily input used by the integral-model construction is supplied by
the actual auxiliary fine model and its proved projective components. -/

theorem provedReferenceFamilyModuliInput : ReferenceFamily.ModuliInput :=
  AbelianModuli.ReferenceFamily.Components.moduli_components_unconditional

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamilyConstructed
