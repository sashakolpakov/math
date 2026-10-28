import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Algebra.Ring.NonZeroDivisors

/-! # Open Principal Ideal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealRestriction.BundleCycles

noncomputable section

section

/-! A regular principal scheme-theoretic image ideal stays regularly
principal on actual affine basic opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} [IsAffine X] (f : Z ⟶ X) [QuasiCompact f]
    (t : Γ(X, ⊤)) (ht : IsRegular t) (hker : RingHom.ker f.appTop.hom = Ideal.span {t})

include ht in
theorem affinePrincipal_regular_restriction (r : Γ(X, ⊤)) :
    IsRegular (X.presheaf.map (homOfLE (X.basicOpen_le r)).op t) := by
  let φ : Γ(X, ⊤) →+* Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, ⊤) Γ(X, X.basicOpen r) := φ.toAlgebra
  let : IsLocalization.Away r Γ(X, X.basicOpen r) := (isAffineOpen_top X).isLocalization_basicOpen r
  have hm : t ∈ nonZeroDivisors Γ(X, ⊤) := isRegular_iff_mem_nonZeroDivisors.mp ht
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (IsLocalization.nonZeroDivisors_le_comap (S := Γ(X, X.basicOpen r)) (M := Submonoid.powers r) hm)

include hker in
theorem affinePrincipal_kernel_restriction (r : Γ(X, ⊤)) :
    RingHom.ker (f.app (X.basicOpen r)).hom =
      Ideal.span {X.presheaf.map (homOfLE (X.basicOpen_le r)).op t} := by
  have h := f.ker.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ r
  have htop : f.ker.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t} :=
    (Scheme.Hom.ker_apply f ⟨⊤, isAffineOpen_top X⟩).trans hker
  have he : f.ker.ideal ⟨X.basicOpen r, (isAffineOpen_top X).basicOpen r⟩ =
      RingHom.ker (f.app (X.basicOpen r)).hom :=
    Scheme.Hom.ker_apply f ⟨X.basicOpen r, (isAffineOpen_top X).basicOpen r⟩
  exact he.symm.trans (h.symm.trans
    ((congrArg (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom) htop).trans
      (by rw [Ideal.map_span, Set.image_singleton])))

end

/-! Regular principal image ideals remain regular and principal on
basic opens inside an arbitrary affine open of the ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    (U : X.affineOpens) (t : Γ(X, U.1)) (ht : IsRegular t)
    (hker : RingHom.ker (f.app U.1).hom = Ideal.span {t})

include ht in
theorem affineOpenPrincipal_regular_restriction (r : Γ(X, U.1)) :
    IsRegular (X.presheaf.map (homOfLE (X.basicOpen_le r)).op t) := by
  let φ : Γ(X, U.1) →+* Γ(X, X.basicOpen r) := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) := φ.toAlgebra
  let : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  have hm : t ∈ nonZeroDivisors Γ(X, U.1) := isRegular_iff_mem_nonZeroDivisors.mp ht
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (IsLocalization.nonZeroDivisors_le_comap (S := Γ(X, X.basicOpen r)) (M := Submonoid.powers r) hm)

include hker in
theorem affineOpenPrincipal_kernel_restriction (r : Γ(X, U.1)) :
    RingHom.ker (f.app (X.basicOpen r)).hom =
      Ideal.span {X.presheaf.map (homOfLE (X.basicOpen_le r)).op t} := by
  have h := f.ker.map_ideal_basicOpen U r
  have hU : f.ker.ideal U = Ideal.span {t} := (Scheme.Hom.ker_apply f U).trans hker
  have he : f.ker.ideal ⟨X.basicOpen r, U.2.basicOpen r⟩ = RingHom.ker (f.app (X.basicOpen r)).hom :=
    Scheme.Hom.ker_apply f ⟨X.basicOpen r, U.2.basicOpen r⟩
  exact he.symm.trans (h.symm.trans
    ((congrArg (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom) hU).trans
      (by rw [Ideal.map_span, Set.image_singleton])))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealRestriction.BundleCycles
