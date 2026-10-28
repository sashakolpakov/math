import OAI.RepresentationTheory.Theta.Geometric.SphericalGU
import OAI.RepresentationTheory.Satake.GL3TorusIwasawa
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Hecke Scalar Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeScalarExtension.Iwasawa

noncomputable section

/-! Identify rational spherical operators after extension to complex
coefficients with operators on the actual complex coset module. -/

open scoped Classical TensorProduct

variable {G : Type*} [Group G] (K : Subgroup G)

def cosetScalarEquiv :
    ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.CosetModule K ≃ₗ[ℂ] RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule K :=
  TensorProduct.finsuppScalarRight ℚ ℂ ℂ (G ⧸ K)

theorem cosetScalarEquiv_tmul_single (x : G ⧸ K) (c : ℂ) :
    cosetScalarEquiv K (c ⊗ₜ[ℚ] Finsupp.single x 1) = Finsupp.single x c := by
  ext y
  simp [cosetScalarEquiv, Finsupp.single_apply]

theorem cosetScalarEquiv_symm_single (x : G ⧸ K) (c : ℂ) :
    (cosetScalarEquiv K).symm (Finsupp.single x c) = c ⊗ₜ[ℚ] Finsupp.single x 1 :=
  TensorProduct.finsuppScalarRight_symm_apply_single (R := ℚ) (S := ℂ) (M := ℂ) x c

def scalarExtendEnd : Module.End ℚ (AbelianScheme.TateComparison.HeckeKernel.CosetModule K) →ₐ[ℚ]
    Module.End ℂ (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule K) :=
  ((cosetScalarEquiv K).conjAlgEquiv ℚ).toAlgHom.comp (Module.End.baseChangeHom ℚ ℂ _)

theorem scalarExtendEnd_translate (g : G) :
    scalarExtendEnd K (AbelianScheme.TateComparison.HeckeKernel.translate K g) = RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.regular K g := by
  apply Finsupp.lhom_ext
  intro x c
  change cosetScalarEquiv K ((AbelianScheme.TateComparison.HeckeKernel.translate K g).baseChange ℂ
    ((cosetScalarEquiv K).symm (Finsupp.single x c))) = _
  rw [cosetScalarEquiv_symm_single, LinearMap.baseChange_tmul, AbelianScheme.TateComparison.HeckeKernel.translate_single,
    cosetScalarEquiv_tmul_single, RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.regular_single]

theorem scalarExtendEnd_spherical (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    scalarExtendEnd K T.val ∈ RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.algebra K := by
  intro A hA
  obtain ⟨g, rfl⟩ := hA
  have h := congrArg (scalarExtendEnd K) (T.property (AbelianScheme.TateComparison.HeckeKernel.translate K g) ⟨g, rfl⟩)
  simpa only [map_mul, scalarExtendEnd_translate] using h

def rationalComplexHecke : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K →ₐ[ℚ] RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.algebra K where
  toFun T := ⟨scalarExtendEnd K T.val, scalarExtendEnd_spherical K T⟩
  map_one' := Subtype.ext (map_one (scalarExtendEnd K))
  map_mul' T U := Subtype.ext (map_mul (scalarExtendEnd K) T.val U.val)
  map_zero' := Subtype.ext (map_zero (scalarExtendEnd K))
  map_add' T U := Subtype.ext (map_add (scalarExtendEnd K) T.val U.val)
  commutes' r := Subtype.ext ((scalarExtendEnd K).commutes r)

theorem rationalComplexHecke_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) (x : G ⧸ K) :
    RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel K (rationalComplexHecke K T) x = (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T x : ℂ) := by
  change cosetScalarEquiv K (T.val.baseChange ℂ
    ((cosetScalarEquiv K).symm (Finsupp.single (QuotientGroup.mk (1 : G)) 1))) x = _
  rw [cosetScalarEquiv_symm_single, LinearMap.baseChange_tmul]
  change TensorProduct.finsuppScalarRight ℚ ℂ ℂ (G ⧸ K)
    ((1 : ℂ) ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T) x = _
  simp

def complexHecke : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K →ₐ[ℂ] RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.algebra K :=
  AlgHom.liftEquiv ℚ ℂ _ _ (rationalComplexHecke K)

theorem complexHecke_tmul (c : ℂ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    complexHecke K (c ⊗ₜ[ℚ] T) = c • rationalComplexHecke K T := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeScalarExtension.Iwasawa
