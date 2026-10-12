// Bundled reference data so the application is complete offline.
// Every entry carries its source so that software-supplied values remain traceable.

const CODATA = 'CODATA 2018 recommended values (NIST)';
const IAU = 'IAU 2015 nominal values / NASA planetary fact sheets';

/** Fundamental constants in SI. `exact` marks defined values of the 2019 SI. */
export const CONSTANTS = {
  c: { name: 'Speed of light in vacuum', value: 299792458, unit: 'm/s', exact: true, src: CODATA },
  G: { name: 'Newtonian constant of gravitation', value: 6.67430e-11, unit: 'm^3/(kg s^2)', rel: 2.2e-5, src: CODATA },
  h: { name: 'Planck constant', value: 6.62607015e-34, unit: 'J s', exact: true, src: CODATA },
  hbar: { name: 'Reduced Planck constant', value: 1.054571817e-34, unit: 'J s', exact: true, src: CODATA },
  k_B: { name: 'Boltzmann constant', value: 1.380649e-23, unit: 'J/K', exact: true, src: CODATA },
  e_c: { name: 'Elementary charge', value: 1.602176634e-19, unit: 'C', exact: true, src: CODATA },
  N_A: { name: 'Avogadro constant', value: 6.02214076e23, unit: '1/mol', exact: true, src: CODATA },
  R_u: { name: 'Molar gas constant', value: 8.314462618, unit: 'J/(mol K)', exact: true, src: CODATA },
  eps_0: { name: 'Vacuum permittivity', value: 8.8541878128e-12, unit: 'F/m', rel: 1.5e-10, src: CODATA },
  mu_0: { name: 'Vacuum permeability', value: 1.25663706212e-6, unit: 'H/m', rel: 1.5e-10, src: CODATA },
  sigma_SB: { name: 'Stefan–Boltzmann constant', value: 5.670374419e-8, unit: 'W/(m^2 K^4)', exact: true, src: CODATA },
  m_e: { name: 'Electron mass', value: 9.1093837015e-31, unit: 'kg', rel: 3e-10, src: CODATA },
  m_p: { name: 'Proton mass', value: 1.67262192369e-27, unit: 'kg', rel: 3.1e-10, src: CODATA },
  m_n: { name: 'Neutron mass', value: 1.67492749804e-27, unit: 'kg', rel: 5.7e-10, src: CODATA },
  alpha_fs: { name: 'Fine-structure constant', value: 7.2973525693e-3, unit: '1', rel: 1.5e-10, src: CODATA },
  a_0: { name: 'Bohr radius', value: 5.29177210903e-11, unit: 'm', rel: 1.5e-10, src: CODATA },
  g_0: { name: 'Standard acceleration of gravity', value: 9.80665, unit: 'm/s^2', exact: true, src: 'CGPM 1901 conventional value' },
  atm: { name: 'Standard atmosphere', value: 101325, unit: 'Pa', exact: true, src: 'CGPM 1954 conventional value' },
};

export const BODIES = {
  sun: { name: 'Sun', GM: 1.32712440018e20, mass: 1.98847e30, radius: 6.957e8, luminosity: 3.828e26, src: IAU },
  mercury: { name: 'Mercury', GM: 2.2032e13, mass: 3.3011e23, radius: 2.4397e6, a: 5.7909e10, ecc: 0.2056, period: 7.6005e6, g: 3.70, src: IAU },
  venus: { name: 'Venus', GM: 3.24859e14, mass: 4.8675e24, radius: 6.0518e6, a: 1.08209e11, ecc: 0.0068, period: 1.94142e7, g: 8.87, rhoAtm: 65, src: IAU },
  earth: { name: 'Earth', GM: 3.986004418e14, mass: 5.9722e24, radius: 6.371e6, a: 1.495978707e11, ecc: 0.0167, period: 3.15581e7, g: 9.80665, rhoAtm: 1.225, scaleHeight: 8500, J2: 1.08263e-3, src: IAU },
  moon: { name: 'Moon', GM: 4.9048695e12, mass: 7.342e22, radius: 1.7374e6, a: 3.844e8, ecc: 0.0549, period: 2.3606e6, g: 1.62, src: IAU },
  mars: { name: 'Mars', GM: 4.282837e13, mass: 6.4171e23, radius: 3.3895e6, a: 2.27939e11, ecc: 0.0934, period: 5.93543e7, g: 3.71, rhoAtm: 0.020, scaleHeight: 11100, src: IAU },
  jupiter: { name: 'Jupiter', GM: 1.26686534e17, mass: 1.8982e27, radius: 6.9911e7, a: 7.7857e11, ecc: 0.0489, period: 3.74336e8, g: 24.79, src: IAU },
  saturn: { name: 'Saturn', GM: 3.7931187e16, mass: 5.6834e26, radius: 5.8232e7, a: 1.43353e12, ecc: 0.0565, period: 9.29292e8, g: 10.44, src: IAU },
  uranus: { name: 'Uranus', GM: 5.793939e15, mass: 8.681e25, radius: 2.5362e7, a: 2.87246e12, ecc: 0.0457, period: 2.65137e9, g: 8.69, src: IAU },
  neptune: { name: 'Neptune', GM: 6.836529e15, mass: 1.02413e26, radius: 2.4622e7, a: 4.49506e12, ecc: 0.0113, period: 5.20042e9, g: 11.15, src: IAU },
  titan: { name: 'Titan', GM: 8.9781e12, mass: 1.3452e23, radius: 2.5747e6, g: 1.352, rhoAtm: 5.4, src: IAU },
};

const H = 'Engineering handbook values at 20 °C unless stated (Perry; CRC Handbook; ASM)';
/** Solids: density kg/m³, Young's modulus Pa, Poisson ratio, yield Pa, conductivity W/(m K), specific heat J/(kg K), expansion 1/K. */
export const MATERIALS = {
  'carbon steel': { rho: 7850, E: 2.07e11, nu: 0.30, yield: 2.5e8, k: 50, cp: 480, alpha: 1.2e-5, src: H },
  'X65 line pipe steel': { rho: 7850, E: 2.07e11, nu: 0.30, yield: 4.48e8, uts: 5.31e8, k: 45, cp: 480, alpha: 1.17e-5, src: 'API 5L minimum specified properties' },
  'stainless steel 316': { rho: 8000, E: 1.93e11, nu: 0.30, yield: 2.05e8, k: 16.3, cp: 500, alpha: 1.6e-5, src: H },
  'aluminium 6061-T6': { rho: 2700, E: 6.89e10, nu: 0.33, yield: 2.76e8, k: 167, cp: 896, alpha: 2.36e-5, src: H },
  'aluminium 7075-T6': { rho: 2810, E: 7.17e10, nu: 0.33, yield: 5.03e8, k: 130, cp: 960, alpha: 2.36e-5, src: H },
  'titanium Ti-6Al-4V': { rho: 4430, E: 1.138e11, nu: 0.342, yield: 8.8e8, k: 6.7, cp: 526, alpha: 8.6e-6, src: H },
  copper: { rho: 8960, E: 1.17e11, nu: 0.34, yield: 7e7, k: 401, cp: 385, alpha: 1.65e-5, sigma_e: 5.96e7, src: H },
  concrete: { rho: 2400, E: 3.0e10, nu: 0.2, yield: 3e7, k: 1.7, cp: 880, alpha: 1.0e-5, src: H },
  'CFRP (quasi-isotropic)': { rho: 1600, E: 7.0e10, nu: 0.30, yield: 6e8, k: 5, cp: 900, alpha: 2e-6, src: H },
  glass: { rho: 2500, E: 7.0e10, nu: 0.22, yield: 5e7, k: 1.0, cp: 840, alpha: 9e-6, src: H },
  silicon: { rho: 2329, E: 1.3e11, nu: 0.28, k: 149, cp: 705, alpha: 2.6e-6, bandgap_eV: 1.12, src: H },
  graphene: { rho: 2267, E: 1.0e12, nu: 0.165, k: 3000, thickness: 3.35e-10, src: 'Lee et al., Science 321 (2008) 385; Balandin, Nature Mater. 10 (2011) 569' },
  'FEP film': { rho: 2150, E: 4.8e8, k: 0.2, eps_r: 2.1, breakdown: 5.5e7, src: 'Fluoropolymer manufacturers\' typical data' },
  polyimide: { rho: 1420, E: 2.5e9, k: 0.12, eps_r: 3.4, breakdown: 2.0e8, src: 'Polyimide film typical data' },
  ice: { rho: 917, E: 9e9, k: 2.2, cp: 2090, src: H },
  'methane hydrate (sI)': { rho: 910, k: 0.5, cp: 2100, latent: 4.38e5, src: 'Sloan & Koh, Clathrate Hydrates of Natural Gases, 3rd ed.' },
  'marine clay (soft)': { rho: 1600, su: 1.0e4, phi_deg: 0, src: 'Typical undrained shear strength, DNV-RP-C212 guidance' },
  'dense sand': { rho: 2000, phi_deg: 38, src: 'Typical friction angle, geotechnical handbooks' },
};

/** Fluids at reference conditions: density, dynamic viscosity, specific heat, conductivity. */
export const FLUIDS = {
  air: { rho: 1.225, mu: 1.81e-5, cp: 1005, k: 0.0257, gamma: 1.4, R: 287.05, M: 0.0289647, src: 'ISO 2533 standard atmosphere, sea level, 15 °C' },
  water: { rho: 998.2, mu: 1.002e-3, cp: 4182, k: 0.598, sigma: 0.0728, src: 'IAPWS-95 at 20 °C, 1 atm' },
  seawater: { rho: 1025, mu: 1.08e-3, cp: 3993, k: 0.596, salinity: 0.035, src: 'TEOS-10 at 20 °C, S = 35 g/kg' },
  'crude oil (light)': { rho: 850, mu: 5e-3, cp: 2000, k: 0.13, sigma: 0.025, src: 'Typical 35° API crude at 40 °C' },
  'natural gas': { rho: 0.8, mu: 1.1e-5, cp: 2200, k: 0.035, gamma: 1.3, M: 0.0185, sg: 0.64, src: 'Typical lean gas at standard conditions' },
  methane: { rho: 0.668, mu: 1.1e-5, cp: 2220, k: 0.034, gamma: 1.31, M: 0.01604, src: 'NIST Chemistry WebBook, 20 °C, 1 atm' },
  hydrogen: { rho: 0.0838, mu: 8.8e-6, cp: 14300, k: 0.183, gamma: 1.405, M: 0.002016, src: 'NIST Chemistry WebBook, 20 °C, 1 atm' },
  'carbon dioxide': { rho: 1.842, mu: 1.47e-5, cp: 844, k: 0.0166, gamma: 1.289, M: 0.04401, src: 'NIST Chemistry WebBook, 20 °C, 1 atm' },
  methanol: { rho: 792, mu: 5.9e-4, cp: 2530, M: 0.03204, src: 'CRC Handbook, 20 °C' },
  'mono-ethylene glycol': { rho: 1113, mu: 1.61e-2, cp: 2400, M: 0.06207, src: 'CRC Handbook, 20 °C' },
  'RO brine (65 g/kg)': { rho: 1047, mu: 1.2e-3, cp: 3850, salinity: 0.065, src: 'Sharqawy et al., Desalination and Water Treatment 16 (2010) 354' },
  mercury: { rho: 13534, mu: 1.526e-3, cp: 139, k: 8.3, sigma: 0.485, src: 'CRC Handbook, 20 °C' },
  glycerol: { rho: 1261, mu: 1.412, cp: 2430, src: 'CRC Handbook, 20 °C' },
};

/** ISO 2533 / US Standard Atmosphere 1976, valid to 32 km. Returns SI values. */
export function atmosphere(z) {
  const g = 9.80665, R = 287.05287;
  let T, p;
  if (z <= 11000) { T = 288.15 - 0.0065 * z; p = 101325 * Math.pow(T / 288.15, g / (R * 0.0065)); }
  else if (z <= 20000) { T = 216.65; p = 22632.06 * Math.exp(-g * (z - 11000) / (R * T)); }
  else { T = 216.65 + 0.001 * (z - 20000); p = 5474.889 * Math.pow(T / 216.65, -g / (R * 0.001)); }
  const rho = p / (R * T), mu = 1.458e-6 * Math.pow(T, 1.5) / (T + 110.4);
  return { T, p, rho, mu, a: Math.sqrt(1.4 * R * T) };
}

/** Seawater density (kg/m³) from temperature (°C) and practical salinity (g/kg), 1 atm — Millero & Poisson (1981). */
export function seawaterDensity(tC, S) {
  const rw = 999.842594 + 6.793952e-2 * tC - 9.09529e-3 * tC ** 2 + 1.001685e-4 * tC ** 3 - 1.120083e-6 * tC ** 4 + 6.536332e-9 * tC ** 5;
  const A = 8.24493e-1 - 4.0899e-3 * tC + 7.6438e-5 * tC ** 2 - 8.2467e-7 * tC ** 3 + 5.3875e-9 * tC ** 4;
  const B = -5.72466e-3 + 1.0227e-4 * tC - 1.6546e-6 * tC ** 2;
  return rw + A * S + B * Math.pow(S, 1.5) + 4.8314e-4 * S * S;
}
/** Dynamic viscosity of water (Pa·s) from temperature (°C) — Vogel–Fulcher–Tammann fit, 0–100 °C. */
export const waterViscosity = tC => 2.414e-5 * Math.pow(10, 247.8 / (tC + 273.15 - 140));

/**
 * Offline gazetteer: named seas, basins and engineering regions with a representative point
 * and climatological defaults. Live connectors replace these values whenever the device is online.
 */
export const GAZETTEER = [
  { name: 'North Sea', lat: 57.0, lon: 2.5, depth: 95, seabedT: 6, sst: 10, Hs: 2.4, Tp: 7.5, current: 0.5, kw: ['north sea', 'norwegian continental shelf', 'ukcs', 'aberdeen', 'stavanger'] },
  { name: 'Norwegian Sea', lat: 65.0, lon: 5.0, depth: 1100, seabedT: -1, sst: 8, Hs: 3.0, Tp: 9, current: 0.6, kw: ['norwegian sea', 'ormen lange', 'aasta hansteen'] },
  { name: 'Barents Sea', lat: 73.0, lon: 30.0, depth: 300, seabedT: 1, sst: 4, Hs: 2.5, Tp: 8, current: 0.4, kw: ['barents'] },
  { name: 'Gulf of Mexico (deepwater)', lat: 27.5, lon: -90.5, depth: 1500, seabedT: 4, sst: 26, Hs: 1.2, Tp: 6, current: 0.8, kw: ['gulf of mexico', 'gom', 'gulf of america', 'mississippi canyon', 'green canyon'] },
  { name: 'Gulf of Guinea', lat: 3.5, lon: 6.0, depth: 1200, seabedT: 4, sst: 28, Hs: 1.3, Tp: 12, current: 0.6, kw: ['gulf of guinea', 'nigeria', 'bonga', 'niger delta', 'west africa', 'angola', 'ghana'] },
  { name: 'Santos Basin (pre-salt)', lat: -25.0, lon: -42.5, depth: 2100, seabedT: 4, sst: 24, Hs: 2.0, Tp: 9, current: 0.7, kw: ['santos basin', 'pre-salt', 'presalt', 'brazil', 'campos'] },
  { name: 'Eastern Mediterranean', lat: 34.0, lon: 33.5, depth: 1700, seabedT: 13.8, sst: 22, Hs: 1.0, Tp: 6, current: 0.2, kw: ['mediterranean', 'cyprus', 'levantine', 'aphrodite', 'leviathan', 'zohr', 'limassol'] },
  { name: 'Arabian Gulf', lat: 26.5, lon: 51.5, depth: 35, seabedT: 22, sst: 28, Hs: 0.7, Tp: 5, current: 0.3, salinity: 42, kw: ['arabian gulf', 'persian gulf', 'qatar', 'abu dhabi', 'uae', 'kuwait', 'saudi', 'jubail', 'ras al khair', 'bahrain'] },
  { name: 'Red Sea', lat: 22.0, lon: 38.0, depth: 500, seabedT: 21.5, sst: 28, Hs: 1.0, Tp: 6, current: 0.2, salinity: 40, kw: ['red sea', 'jeddah', 'neom', 'yanbu', 'shuaiba'] },
  { name: 'Caspian Sea', lat: 41.0, lon: 51.0, depth: 200, seabedT: 6, sst: 15, Hs: 1.2, Tp: 6, current: 0.2, salinity: 13, kw: ['caspian', 'kashagan', 'azeri'] },
  { name: 'South China Sea', lat: 12.0, lon: 113.0, depth: 1200, seabedT: 4, sst: 28, Hs: 1.5, Tp: 7, current: 0.5, kw: ['south china sea', 'malaysia', 'vietnam', 'brunei', 'sabah'] },
  { name: 'North West Shelf (Australia)', lat: -19.5, lon: 116.0, depth: 130, seabedT: 12, sst: 27, Hs: 1.5, Tp: 9, current: 0.5, kw: ['north west shelf', 'australia', 'browse', 'gorgon', 'perth'] },
  { name: 'North Atlantic', lat: 45.0, lon: -30.0, depth: 4000, seabedT: 2.5, sst: 15, Hs: 3.2, Tp: 10, current: 0.4, kw: ['north atlantic', 'atlantic ocean'] },
  { name: 'Pacific Ocean (central)', lat: 0.0, lon: -150.0, depth: 4500, seabedT: 1.5, sst: 27, Hs: 2.2, Tp: 10, current: 0.3, kw: ['pacific'] },
  { name: 'Arctic Ocean', lat: 85.0, lon: 0.0, depth: 3500, seabedT: -0.8, sst: -1.5, Hs: 1.0, Tp: 6, current: 0.1, kw: ['arctic'] },
  { name: 'Southern Ocean', lat: -60.0, lon: 0.0, depth: 4000, seabedT: 0, sst: 2, Hs: 4.5, Tp: 11, current: 0.6, kw: ['southern ocean', 'antarctic'] },
  { name: 'Mariana Trench', lat: 11.35, lon: 142.2, depth: 10900, seabedT: 2.5, sst: 29, Hs: 2.0, Tp: 9, current: 0.1, kw: ['mariana', 'challenger deep'] },
  { name: 'Baltic Sea', lat: 58.0, lon: 20.0, depth: 55, seabedT: 5, sst: 9, Hs: 1.0, Tp: 5, current: 0.1, salinity: 7, kw: ['baltic'] },
  { name: 'Black Sea', lat: 43.0, lon: 34.0, depth: 1250, seabedT: 9, sst: 15, Hs: 1.0, Tp: 5.5, current: 0.2, salinity: 18, kw: ['black sea', 'sakarya'] },
  { name: 'Offshore California', lat: 33.5, lon: -118.5, depth: 800, seabedT: 5, sst: 17, Hs: 1.5, Tp: 11, current: 0.2, kw: ['california', 'carlsbad', 'san diego', 'los angeles'] },
];

/** Typical named land sites for experiments that depend on altitude and weather. */
export const SITES = [
  { name: 'Sea level (standard day)', lat: 0, lon: 0, alt: 0 }, { name: 'Denver, USA', lat: 39.74, lon: -104.99, alt: 1609 },
  { name: 'La Paz, Bolivia', lat: -16.5, lon: -68.15, alt: 3640 }, { name: 'Geneva (CERN), Switzerland', lat: 46.23, lon: 6.05, alt: 430 },
  { name: 'Cape Canaveral, USA', lat: 28.39, lon: -80.6, alt: 3 }, { name: 'Kourou, French Guiana', lat: 5.24, lon: -52.77, alt: 10 },
  { name: 'Mauna Kea, USA', lat: 19.82, lon: -155.47, alt: 4205 }, { name: 'Atacama (ALMA), Chile', lat: -23.03, lon: -67.75, alt: 5058 },
];

/**
 * Environmental bindings. A model input may declare `env: '<key>'`; the engine then fills it
 * from a live connector (labelled SOFTWARE-RETRIEVED) or from the gazetteer (SOFTWARE-ESTIMATED).
 */
export const ENV_KEYS = {
  water_depth: { name: 'Water depth', unit: 'm' }, seabed_temp: { name: 'Seabed temperature', unit: 'K' },
  sea_surface_temp: { name: 'Sea-surface temperature', unit: 'K' }, wave_height: { name: 'Significant wave height', unit: 'm' },
  wave_period: { name: 'Peak wave period', unit: 's' }, current_speed: { name: 'Current speed', unit: 'm/s' },
  salinity: { name: 'Salinity', unit: 'g/kg' }, air_temp: { name: 'Air temperature', unit: 'K' },
  air_pressure: { name: 'Surface air pressure', unit: 'Pa' }, wind_speed: { name: 'Wind speed at 10 m', unit: 'm/s' },
  humidity: { name: 'Relative humidity', unit: '1' }, elevation: { name: 'Ground elevation', unit: 'm' },
  air_density: { name: 'Air density', unit: 'kg/m^3' }, kp_index: { name: 'Planetary K index', unit: '1' },
  solar_wind_speed: { name: 'Solar-wind speed', unit: 'm/s' }, latitude: { name: 'Latitude', unit: 'deg' },
  gravity: { name: 'Local gravitational acceleration', unit: 'm/s^2' },
};

/** Normal gravity on the WGS-84 ellipsoid (Somigliana) with free-air correction. */
export function localGravity(latDeg, alt = 0) {
  const s = Math.sin(latDeg * Math.PI / 180) ** 2;
  return 9.7803253359 * (1 + 0.00193185265241 * s) / Math.sqrt(1 - 0.00669437999013 * s) - 3.086e-6 * alt;
}
