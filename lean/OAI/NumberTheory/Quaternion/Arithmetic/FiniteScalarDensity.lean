import OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation

/-! # Finite Scalar Density -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteScalarDensity

noncomputable section

/-! Weak approximation for any injectively indexed finite family of
finite completions, and for finite affine parameter spaces over them. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type*} [Field F] [NumberField F] {ι : Type*} [Fintype ι]

def finiteScalarDiagonal (v : ι → HeightOneSpectrum (𝓞 F)) :
    F →+* (∀ i, (v i).adicCompletion F) := RingHom.pi (fun i => algebraMap F ((v i).adicCompletion F))

theorem denseRange_finiteScalarDiagonal (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) : DenseRange (finiteScalarDiagonal v) := by
  let T := Finset.univ.image v
  let f : ι → T := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hfinj : Function.Injective f := fun i j hij => hv (congrArg Subtype.val hij)
  have hfsurj : Function.Surjective f := by
    intro w
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp w.property
    exact ⟨i, Subtype.ext hi⟩
  let e := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let E := Homeomorph.piCongrLeft (Y := fun w : T => w.val.adicCompletion F) e
  have hd := E.symm.surjective.denseRange.comp (ScalarApproximation.denseRange_scalarProjection T) E.symm.continuous
  apply hd.mono
  rintro x ⟨a, rfl⟩
  exact ⟨a.val, rfl⟩

theorem denseRange_finiteAffineDiagonal (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (m : ℕ) :
    DenseRange (fun a : Fin m → F => fun i j => algebraMap F ((v i).adicCompletion F) (a j)) := by
  have hd := DenseRange.piMap (fun _ : Fin m => denseRange_finiteScalarDiagonal v hv)
  let swap : (Fin m → ∀ i, (v i).adicCompletion F) → (∀ i, Fin m → (v i).adicCompletion F) :=
    fun a i j => a j i
  have hc : Continuous swap := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  have hs : Function.Surjective swap := fun a => ⟨fun j i => a i j, rfl⟩
  exact hs.denseRange.comp hd hc

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteScalarDensity
