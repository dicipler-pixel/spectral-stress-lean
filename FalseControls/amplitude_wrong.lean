import SpectralStress.Basic
-- The amplitude is −5√2/16, not −√2/4: the recessive pair adds −√2/16.
example : (SpectralStress.ρdom - SpectralStress.ρmid) * ((√2 - 1) / 16) = -5 * √2 / 16 := by
  rw [SpectralStress.t_dom_mid]; ring_nf; norm_num
