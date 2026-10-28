import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Chain Degree Transport -/

namespace OAI.AlgebraicTopology.Products.ChainDegreeTransport.Cohomology

noncomputable section

/-!
Equality-of-degree transport for the actual cycle and homology modules of a
chain complex. The transported classes retain their concrete representatives.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R] (C : ChainComplex (ModuleCat.{0} R) ℕ)
  {m n k : ℕ}

/-- Equality transport in the genuine cycle submodule. -/
def chainCycleCast (h : m = n) : Cohomology.Singular.ChainRepresentatives.chainCycles C m →ₗ[R] Cohomology.Singular.ChainRepresentatives.chainCycles C n := by
  subst n
  exact LinearMap.id

/-- Equality transport in the actual categorical homology module. -/
def chainHomologyCast (h : m = n) : C.homology m →ₗ[R] C.homology n :=
  (eqToHom (congrArg (fun j => C.homology j) h)).hom

@[simp]
theorem chainCycleCast_rfl (n : ℕ) :
    chainCycleCast C (rfl : n = n) = LinearMap.id := rfl

@[simp]
theorem chainHomologyCast_rfl (n : ℕ) :
    chainHomologyCast C (rfl : n = n) = LinearMap.id := rfl

/-- A transported cycle has the transported actual chain as its value. -/
@[simp]
theorem chainCycleCast_val (h : m = n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C m) :
    (chainCycleCast C h z).val = (eqToHom (congrArg C.X h)) z.val := by
  subst n
  rfl

/-- Homology degree transport sends a represented class to the transported cycle. -/
@[simp]
theorem chainHomologyCast_class (h : m = n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C m) :
    chainHomologyCast C h (Cohomology.Singular.ChainRepresentatives.chainClass C m z) =
      Cohomology.Singular.ChainRepresentatives.chainClass C n (chainCycleCast C h z) := by
  subst n
  rfl

@[simp]
theorem chainCycleCast_symm_apply (h : m = n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C m) :
    chainCycleCast C h.symm (chainCycleCast C h z) = z := by
  subst n
  rfl

@[simp]
theorem chainHomologyCast_symm_apply (h : m = n) (z : C.homology m) :
    chainHomologyCast C h.symm (chainHomologyCast C h z) = z := by
  subst n
  rfl

@[simp]
theorem chainCycleCast_trans (h : m = n) (g : n = k) (z : Cohomology.Singular.ChainRepresentatives.chainCycles C m) :
    chainCycleCast C g (chainCycleCast C h z) = chainCycleCast C (h.trans g) z := by
  subst n
  subst k
  rfl

@[simp]
theorem chainHomologyCast_trans (h : m = n) (g : n = k) (z : C.homology m) :
    chainHomologyCast C g (chainHomologyCast C h z) =
      chainHomologyCast C (h.trans g) z := by
  subst n
  subst k
  rfl

end

end OAI.AlgebraicTopology.Products.ChainDegreeTransport.Cohomology
