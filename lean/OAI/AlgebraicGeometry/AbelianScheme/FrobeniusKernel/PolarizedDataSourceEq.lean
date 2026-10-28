import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Polarized Data Source Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedDataSourceEq.Construction

noncomputable section

/-! Transport a full polarized isomorphism through a proved equality
of source data, without recomputing its geometric components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

def polarizedActionIso_of_source_eq (A A' B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
    (h : A = A') (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B) : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A' B :=
  h ▸ e

def polarizedActionIso_of_target_eq (A B B' : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
    (h : B = B') (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B) : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B' :=
  h ▸ e

theorem polarizedActionData_pullback_congr (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S)
    {f f' : T ⟶ S} (h : f = f') : A.pullback f = A.pullback f' :=
  congrArg (fun t => A.pullback t) h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedDataSourceEq.Construction
