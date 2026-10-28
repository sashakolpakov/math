import OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent
import OAI.ArithmeticGeometry.Descent.CMVariety.Abelian
import OAI.ArithmeticGeometry.Descent.CMVariety.Moduli

/-! # Established Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedDescent

/-! Apply the proved CMAbelianVariety theorems with their full arithmetic-model and
actual moduli-point conclusions. -/

theorem abelian_descent : Descent.AbelianInput :=
  ArithmeticGeometry.Descent.CMVariety.Abelian.cm_abelian_variety_has_number_field_model

theorem moduli_descent : Descent.ModuliInput :=
  ArithmeticGeometry.Descent.CMVariety.Moduli.Abelian.cm_moduli_point_is_algebraic

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedDescent
