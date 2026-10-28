import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Forms Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf

noncomputable section

/-!
# Actual native frame-form presheaves are sheaves

Continuity of the constructed frame functor makes its ambient functions
a sheaf. Each native coordinate form term tensors those functions with
a finite free exterior power. The proved finite tensor result therefore
applies to every term of the original frame resolution.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a

omit [Fintype σ] in
theorem functions_isSheaf : Presheaf.IsSheaf J F :=
  (Functor.CrystallineFrameFunctor.functor p k B σ a).op_comp_isSheaf_of_isSheaf J J
    (Site.functions p k X) (FunctionsSheaf.CrystallineFunctionsSheaf.functions_isSheaf p k X)

def termTensorIso (n : ℕ) : (Resolution.CrystallineFrameResolution.complex p k B σ a).X n ≅
    F ⋙ Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

theorem term_isSheaf (n : ℕ) :
    Presheaf.IsSheaf J ((Resolution.CrystallineFrameResolution.complex p k B σ a).X n) := by
  let H := ⋀[W]^n (σ →₀ W)
  let b := Module.Free.chooseBasis W H
  let : Fintype (Module.Free.ChooseBasisIndex W H) := Fintype.ofFinite _
  have hs : Presheaf.IsSheaf J (F ⋙ Finite.TensorSheaf.FiniteTensorSheaf.tensor W H) :=
    Finite.TensorSheaf.FiniteTensorSheaf.isSheaf W (Module.Free.ChooseBasisIndex W H) H b J F
      (functions_isSheaf p k B σ a)
  exact (Presheaf.isSheaf_of_iso_iff (termTensorIso p k B σ a n)).mpr hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf
