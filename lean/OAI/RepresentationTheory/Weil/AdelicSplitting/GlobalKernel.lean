import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel

/-! # Global Kernel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.GlobalKernel.Construction

noncomputable section

/-! The kernel of the actual adelic projection consists of global circle
scalars. The finite scalar product is constructed from a restricted
representative; its value is not presumed to be one. -/

open Filter
open scoped Classical

section Scalars
variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def globalScalar (w : ArchimedeanAdeles.Construction.Places F) : Circle →* Vacuum.Construction.GlobalCover F N ψ :=
  (CentralProduct.Construction.includeCover (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) w).comp (Vacuum.Construction.scalarAt F N ψ w)

theorem globalScalar_place_independent (v w : ArchimedeanAdeles.Construction.Places F) (z : Circle) :
    globalScalar F N ψ v z = globalScalar F N ψ w z :=
  CentralProduct.Construction.includeCover_scalar_eq (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) v w z

theorem globalScalar_projects (w : ArchimedeanAdeles.Construction.Places F) (z : Circle) :
    Vacuum.Construction.globalProjection F N ψ (globalScalar F N ψ w z) = 1 := by
  change Vacuum.Construction.globalProjection F N ψ (Vacuum.Construction.globalInclude F N ψ w (Vacuum.Construction.scalarAt F N ψ w z)) = 1
  rw [Vacuum.Construction.globalProjection_include]
  change RestrictedLimits.Construction.includePlace (Vacuum.Construction.symplecticIntegral F N) w
    (Oscillator.Construction.localProjection (ArchimedeanAdeles.Construction.Completion F w) N (Characters.Construction.localAdditiveCharacter F ψ w) (Oscillator.Construction.localScalar _ _ _ z)) = 1
  rw [Oscillator.Construction.localProjection_scalar, map_one]

theorem assemble_restricted_scalar (w : ArchimedeanAdeles.Construction.Places F)
    (a : Rational.Construction.RestrictedCover F N ψ) (z : ArchimedeanAdeles.Construction.Places F → Circle)
    (ha : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) :
    ∃ c : Circle, globalScalar F N ψ w c = Rational.Construction.assembleGlobalCover F N ψ a := by
  have hs := eventually_cofinite.mp (AdelicSplitting.Scalars.Construction.restricted_scalar_eventually_one F N ψ a z ha)
  let s := hs.toFinset
  have hz : ∀ v ∉ s, z v = 1 := by
    intro v hv
    exact by simpa using hs.mem_toFinset.not.mp hv
  have heq := CentralProduct.Construction.scalar_family_eq_finite (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) s z hz a ha
  refine ⟨((s.toList.map (fun v => (v, z v))).map Prod.snd).prod, ?_⟩
  change CentralProduct.Construction.includeCover (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) w
    (Vacuum.Construction.scalarAt F N ψ w _) = CentralProduct.Construction.assembleCover (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) a
  rw [heq, CentralProduct.Construction.assemble_finiteScalarFamily]

end Scalars

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hN D in
theorem normalized_globalProjection_kernel_circle (w : ArchimedeanAdeles.Construction.Places F)
    (a : Vacuum.Construction.GlobalCover F (n * m) C.ψ) (ha : Vacuum.Construction.globalProjection F (n * m) C.ψ a = 1) :
    ∃ z : Circle, globalScalar F (n * m) C.ψ w z = a := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CentralProduct.Construction.scalarKernel (Vacuum.Construction.coverIntegral F (n * m) C.ψ)
    (Vacuum.Construction.scalarAt F (n * m) C.ψ)) a
  have hp (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.projectionAt F (n * m) C.ψ v (b v) = 1 := by
    have h := congrArg (fun x : Vacuum.Construction.AdelicSymplectic F (n * m) => x v) ha
    exact h
  choose z hz using (fun v => LocalKernel.Construction.normalized_localCover_kernel_circle F d hd n m hN H K C P D v (b v) (hp v))
  exact assemble_restricted_scalar F (n * m) C.ψ w b z (fun v => (hz v).symm)

include hN D in
theorem rationalGraph_identity_is_scalar (w : ArchimedeanAdeles.Construction.Places F)
    (a : Vacuum.Construction.GlobalCover F (n * m) C.ψ) (ha : (1, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ) :
    ∃ z : Circle, globalScalar F (n * m) C.ψ w z = a := by
  have hp := Rational.Construction.rationalGraph_covers F (n * m) C.ψ ha
  change Vacuum.Construction.globalProjection F (n * m) C.ψ a = Vacuum.Construction.rationalSymplectic F (n * m) 1 at hp
  rw [map_one] at hp
  exact normalized_globalProjection_kernel_circle F d hd n m hN H K C P D w a hp

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.GlobalKernel.Construction
