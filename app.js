/**
 * PosteTrack Pro - Control de Obra, Centro de Reportes Formales, Google Maps (GPS) y Plano Georreferenciado
 * Padrón Oficial: 524 Postes (9m) + 131 Cámaras (13m) = 655 Puntos
 */

const STORAGE_KEY = 'postes_tracker_master_db_v3';

// Definición oficial de etapas de obra
const STAGES_CONFIG = {
  terminado: { name: 'Terminado', color: '#10b981', badgeBg: 'bg-emerald-100', badgeText: 'text-emerald-800', border: 'border-emerald-300', dot: 'bg-emerald-500' },
  izado_sin_solado: { name: 'Izado sin Solado', color: '#0284c7', badgeBg: 'bg-sky-100', badgeText: 'text-sky-800', border: 'border-sky-300', dot: 'bg-sky-500' },
  falta_solado: { name: 'Falta Solado', color: '#8b5cf6', badgeBg: 'bg-purple-100', badgeText: 'text-purple-800', border: 'border-purple-300', dot: 'bg-purple-500' },
  excavado: { name: 'Excavado', color: '#eab308', badgeBg: 'bg-yellow-100', badgeText: 'text-yellow-800', border: 'border-yellow-300', dot: 'bg-yellow-500' },
  corte: { name: 'En Corte', color: '#f97316', badgeBg: 'bg-orange-100', badgeText: 'text-orange-800', border: 'border-orange-300', dot: 'bg-orange-500' },
  pendiente: { name: 'Sin Iniciar', color: '#64748b', badgeBg: 'bg-slate-100', badgeText: 'text-slate-700', border: 'border-slate-300', dot: 'bg-slate-400' }
};

// Estado global
let polesState = [];
let activeTypeFilter = 'all'; // 'all' | '9m' | '13m'
let currentOpenPoleIndex = 0;
let utmZone = 18; // Zona UTM por defecto (18S)

// Filtros para Centro de Reportes (Soporte de Selección Múltiple)
let reportMultiFilters = {
  types: new Set(['9m', '13m']),
  stages: new Set(['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente']),
  crews: new Set(['ALL']), // 'ALL' o conjunto de nombres de cuadrillas
  photos: 'all' // 'all' | 'with_photos' | 'without_photos'
};

// Variables para Mapa Leaflet
let leafletMap = null;
let leafletMarkersLayer = null;
let leafletTileSatellite = null;
let leafletTileStreets = null;
let currentMapMode = 'satellite'; // 'satellite' | 'streets' | 'canvas'

// Variables para Canvas 2D alternativo
let mapZoom = 1;
let mapOffsetX = 0;
let mapOffsetY = 0;
let isDraggingMap = false;
let startDragX = 0;
let startDragY = 0;
let hoveredPole = null;
let mapLabelMode = 'short'; // 'short' (P01/C01) | 'full' (POSTE 01) | 'none'
let touchStartDist = 0;
let touchStartZoom = 1;

// ==========================================
// CONVERSIÓN DE COORDENADAS UTM A LAT/LNG (WGS84)
// ==========================================
function utmToLatLng(easting, northing, zone = 18, isSouth = true) {
  if (!easting || !northing) return { lat: 0, lng: 0, googleMapsUrl: '#' };

  const a = 6378137;
  const f = 1 / 298.257223563;
  const k0 = 0.9996;
  const e = Math.sqrt(2 * f - f * f);
  const e1 = (1 - Math.sqrt(1 - e * e)) / (1 + Math.sqrt(1 - e * e));

  const x = easting - 500000;
  const y = isSouth ? northing - 10000000 : northing;

  const m = y / k0;
  const mu = m / (a * (1 - (e * e) / 4 - (3 * Math.pow(e, 4)) / 64 - (5 * Math.pow(e, 6)) / 256));

  const phi1 = mu + ((3 * e1) / 2 - (27 * Math.pow(e1, 3)) / 32) * Math.sin(2 * mu)
    + ((21 * Math.pow(e1, 2)) / 16 - (55 * Math.pow(e1, 4)) / 32) * Math.sin(4 * mu)
    + ((151 * Math.pow(e1, 3)) / 96) * Math.sin(6 * mu);

  const n1 = a / Math.sqrt(1 - Math.pow(e * Math.sin(phi1), 2));
  const t1 = Math.pow(Math.tan(phi1), 2);
  const c1 = (e * e / (1 - e * e)) * Math.pow(Math.cos(phi1), 2);
  const r1 = a * (1 - e * e) / Math.pow(1 - Math.pow(e * Math.sin(phi1), 2), 1.5);
  const d = x / (n1 * k0);

  const lat = phi1 - (n1 * Math.tan(phi1) / r1) * (
    Math.pow(d, 2) / 2
    - (5 + 3 * t1 + 10 * c1 - 4 * Math.pow(c1, 2) - 9 * (e * e / (1 - e * e))) * Math.pow(d, 4) / 24
    + (61 + 90 * t1 + 298 * c1 + 45 * Math.pow(t1, 2) - 252 * (e * e / (1 - e * e)) - 3 * Math.pow(c1, 2)) * Math.pow(d, 6) / 720
  );

  const lon = (
    d - (1 + 2 * t1 + c1) * Math.pow(d, 3) / 6
    + (5 - 2 * c1 + 28 * t1 - 3 * Math.pow(c1, 2) + 8 * (e * e / (1 - e * e)) + 24 * Math.pow(t1, 2)) * Math.pow(d, 5) / 120
  ) / Math.cos(phi1);

  const lambda0 = ((zone - 1) * 6 - 180 + 3) * (Math.PI / 180);

  const finalLat = (lat * 180) / Math.PI;
  const finalLng = ((lambda0 + lon) * 180) / Math.PI;

  return {
    lat: finalLat,
    lng: finalLng,
    googleMapsUrl: `https://www.google.com/maps?q=${finalLat.toFixed(6)},${finalLng.toFixed(6)}`
  };
}

// Inicial corta (P01, C01)
function getShortPoleName(fullName) {
  if (!fullName) return '';
  if (fullName.startsWith('POSTE ')) {
    const num = fullName.replace('POSTE ', '').trim();
    return `P${num}`;
  }
  if (fullName.startsWith('CAMARA ')) {
    const num = fullName.replace('CAMARA ', '').trim();
    return `C${num}`;
  }
  return fullName;
}

// ==========================================
// INICIALIZACIÓN A PRUEBA DE FALLOS
// ==========================================
function startPosteTrackApp() {
  try {
    initPolesDatabase();
  } catch (e) {
    console.error('Error initPolesDatabase:', e);
  }

  try {
    setupEventListeners();
  } catch (e) {
    console.error('Error setupEventListeners:', e);
  }

  try {
    setupCanvasMap();
  } catch (e) {
    console.error('Error setupCanvasMap:', e);
  }

  try {
    updateDashboard();
  } catch (e) {
    console.error('Error updateDashboard:', e);
  }

  try {
    switchPolesViewMode(currentPolesViewMode);
    renderPolesTable();
  } catch (e) {
    console.error('Error renderPolesTable:', e);
  }

  try {
    startLiveAutoSync();
  } catch (e) {
    console.error('Error startLiveAutoSync:', e);
  }

  try {
    if (window.lucide && typeof window.lucide.createIcons === 'function') {
      window.lucide.createIcons();
    }
  } catch (e) {}
}

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', startPosteTrackApp);
} else {
  startPosteTrackApp();
}

window.addEventListener('load', () => {
  if (polesState.length === 0) startPosteTrackApp();
  try {
    if (window.lucide && typeof window.lucide.createIcons === 'function') {
      window.lucide.createIcons();
    }
  } catch (e) {}
});

function initPolesDatabase() {
  const basePoles = [];

  // Agregar 524 Postes de 9m
  if (typeof RAW_POLES_9M_DATA !== 'undefined') {
    RAW_POLES_9M_DATA.forEach((p, idx) => {
      const gps = utmToLatLng(p.x, p.y, utmZone, true);
      basePoles.push({
        ...p,
        orderIndex: idx + 1,
        shortName: getShortPoleName(p.name),
        category: '9m',
        stage: 'pendiente',
        lat: gps.lat,
        lng: gps.lng,
        googleMapsUrl: gps.googleMapsUrl,
        crew: '',
        installedAt: '',
        installNotes: '',
        photos: []
      });
    });
  }

  // Agregar 131 Cámaras de 13m
  if (typeof RAW_POLES_13M_CAMERAS_DATA !== 'undefined') {
    RAW_POLES_13M_CAMERAS_DATA.forEach((c, idx) => {
      const gps = utmToLatLng(c.x, c.y, utmZone, true);
      basePoles.push({
        ...c,
        orderIndex: idx + 1,
        shortName: getShortPoleName(c.name),
        category: '13m',
        stage: 'pendiente',
        lat: gps.lat,
        lng: gps.lng,
        googleMapsUrl: gps.googleMapsUrl,
        crew: '',
        installedAt: '',
        installNotes: '',
        photos: []
      });
    });
  }

  const saved = localStorage.getItem(STORAGE_KEY);
  if (saved) {
    try {
      const savedMap = JSON.parse(saved);
      polesState = basePoles.map(pole => {
        const itemSaved = savedMap[pole.id];
        if (itemSaved) {
          return {
            ...pole,
            stage: itemSaved.stage || (itemSaved.status === 'installed' ? 'terminado' : 'pendiente'),
            crew: itemSaved.crew || '',
            installedAt: itemSaved.installedAt || '',
            installNotes: itemSaved.installNotes || '',
            photos: Array.isArray(itemSaved.photos) ? itemSaved.photos : []
          };
        }
        return pole;
      });
    } catch (e) {
      console.error('Error cargando estado:', e);
      polesState = basePoles;
    }
  } else {
    polesState = basePoles;
    savePolesToStorage();
  }

  populateCrewFilters();
}

function savePolesToStorage() {
  const saveMap = {};
  polesState.forEach(p => {
    if (p.stage !== 'pendiente' || p.crew || p.installedAt || p.installNotes || (p.photos && p.photos.length > 0)) {
      saveMap[p.id] = {
        stage: p.stage,
        crew: p.crew,
        installedAt: p.installedAt,
        installNotes: p.installNotes,
        photos: p.photos || []
      };
    }
  });
  localStorage.setItem(STORAGE_KEY, JSON.stringify(saveMap));
}

function populateCrewFilters() {
  const crewSelect = document.getElementById('selectCrewFilter');
  const crewsSet = new Set(['Cuadrilla Alfa', 'Cuadrilla Beta', 'Cuadrilla Gamma', 'Contratista Norte', 'Contratista Sur']);
  polesState.forEach(p => {
    if (p.crew && p.crew.trim()) crewsSet.add(p.crew.trim());
  });

  if (crewSelect) {
    const currentVal = crewSelect.value;
    crewSelect.innerHTML = '<option value="">Todas las Cuadrillas</option>';
    crewsSet.forEach(c => {
      const opt = document.createElement('option');
      opt.value = c;
      opt.textContent = c;
      if (c === currentVal) opt.selected = true;
      crewSelect.appendChild(opt);
    });
  }

  populateReportCrewFilter(crewsSet);
}

function populateReportCrewFilter(crewsSetParam = null) {
  const repCrewSelect = document.getElementById('repFilterCrew');
  const repCrewContainer = document.getElementById('repCrewMultiCheckboxesContainer');
  const crewsSet = crewsSetParam || new Set(['Cuadrilla Alfa', 'Cuadrilla Beta', 'Cuadrilla Gamma', 'Contratista Norte', 'Contratista Sur']);
  
  if (!crewsSetParam) {
    polesState.forEach(p => {
      if (p.crew && p.crew.trim()) crewsSet.add(p.crew.trim());
    });
  }

  // 1. Select Dropdown
  if (repCrewSelect) {
    repCrewSelect.innerHTML = '<option value="ALL">Todas las Cuadrillas</option>';
    crewsSet.forEach(c => {
      const opt = document.createElement('option');
      opt.value = c;
      opt.textContent = c;
      repCrewSelect.appendChild(opt);
    });
  }

  // 2. Multi-Checkboxes Popover
  if (repCrewContainer) {
    repCrewContainer.innerHTML = '';

    const allLabel = document.createElement('label');
    allLabel.className = 'flex items-center gap-1.5 p-1 rounded-lg hover:bg-slate-50 cursor-pointer font-black text-slate-900 border-b border-slate-100 pb-1.5';
    allLabel.innerHTML = `
      <input type="checkbox" id="chkCrew_ALL" value="ALL" ${reportMultiFilters.crews.has('ALL') ? 'checked' : ''} onchange="handleReportCrewCheckboxToggle('ALL', this.checked)" class="w-3.5 h-3.5 rounded text-indigo-600 focus:ring-indigo-500">
      <span>Todas las Cuadrillas</span>
    `;
    repCrewContainer.appendChild(allLabel);

    crewsSet.forEach(c => {
      const isChecked = reportMultiFilters.crews.has('ALL') || reportMultiFilters.crews.has(c);
      const label = document.createElement('label');
      label.className = 'flex items-center gap-1.5 p-1 rounded-lg hover:bg-slate-50 cursor-pointer font-bold text-slate-700';
      label.innerHTML = `
        <input type="checkbox" data-crew="${escapeHtml(c)}" value="${escapeHtml(c)}" ${isChecked ? 'checked' : ''} onchange="handleReportCrewCheckboxToggle('${escapeHtml(c)}', this.checked)" class="w-3.5 h-3.5 rounded text-indigo-600 focus:ring-indigo-500 crew-chk-item">
        <span>${escapeHtml(c)}</span>
      `;
      repCrewContainer.appendChild(label);
    });
  }

  updateCrewSelectionBadge();
}

function updateCrewSelectionBadge() {
  const badgeTxt = document.getElementById('txtSelectedCrewsCount');
  if (!badgeTxt) return;

  if (reportMultiFilters.crews.has('ALL')) {
    badgeTxt.textContent = 'Todas';
  } else {
    const size = reportMultiFilters.crews.size;
    if (size === 0) badgeTxt.textContent = 'Ninguna';
    else if (size === 1) badgeTxt.textContent = Array.from(reportMultiFilters.crews)[0];
    else badgeTxt.textContent = `${size} cuadrillas`;
  }
}

window.handleToggleCrewDropdown = function() {
  const container = document.getElementById('repCrewMultiCheckboxesContainer');
  if (container) container.classList.toggle('hidden');
};

window.handleReportCrewSelectChange = function() {
  const repCrewSelect = document.getElementById('repFilterCrew');
  if (!repCrewSelect) return;

  const val = repCrewSelect.value;
  if (val === 'ALL') {
    reportMultiFilters.crews = new Set(['ALL']);
  } else {
    reportMultiFilters.crews = new Set([val]);
  }

  const chkAll = document.getElementById('chkCrew_ALL');
  if (chkAll) chkAll.checked = val === 'ALL';

  document.querySelectorAll('.crew-chk-item').forEach(chk => {
    chk.checked = val === 'ALL' || chk.value === val;
  });

  updateCrewSelectionBadge();
  renderReportsView();
};

window.handleReportCrewCheckboxToggle = function(crewName, isChecked) {
  const chkAll = document.getElementById('chkCrew_ALL');
  const allCrewChks = document.querySelectorAll('.crew-chk-item');

  if (crewName === 'ALL') {
    if (isChecked) {
      reportMultiFilters.crews = new Set(['ALL']);
      allCrewChks.forEach(chk => chk.checked = true);
    } else {
      reportMultiFilters.crews.clear();
      allCrewChks.forEach(chk => chk.checked = false);
    }
  } else {
    if (reportMultiFilters.crews.has('ALL')) {
      reportMultiFilters.crews.clear();
      allCrewChks.forEach(chk => {
        if (chk.value !== crewName && chk.checked) {
          reportMultiFilters.crews.add(chk.value);
        }
      });
    }

    if (isChecked) {
      reportMultiFilters.crews.add(crewName);
    } else {
      reportMultiFilters.crews.delete(crewName);
    }

    if (chkAll) chkAll.checked = false;
  }

  updateCrewSelectionBadge();
  renderReportsView();
};

// ==========================================
// CÁLCULO DE DASHBOARD
// ==========================================
function updateDashboard() {
  const total = polesState.length; // 655

  const counts = {
    terminado: 0,
    izado_sin_solado: 0,
    falta_solado: 0,
    excavado: 0,
    corte: 0,
    pendiente: 0
  };

  let totalPhotos = 0;
  let terminados9m = 0;
  let terminados13m = 0;

  polesState.forEach(p => {
    const st = p.stage || 'pendiente';
    if (counts[st] !== undefined) counts[st]++;
    else counts.pendiente++;

    if (p.photos && p.photos.length > 0) totalPhotos += p.photos.length;

    if (st === 'terminado') {
      if (p.category === '9m') terminados9m++;
      if (p.category === '13m') terminados13m++;
    }
  });

  // KPIs
  const setTxt = (id, val) => {
    const el = document.getElementById(id);
    if (el) el.textContent = val;
  };

  setTxt('kpiTerminados', counts.terminado.toLocaleString());
  setTxt('kpiIzadoSinSolado', counts.izado_sin_solado.toLocaleString());
  setTxt('kpiFaltaSolado', counts.falta_solado.toLocaleString());
  setTxt('kpiExcavados', counts.excavado.toLocaleString());
  setTxt('kpiEnCorte', counts.corte.toLocaleString());
  setTxt('kpiPendientes', counts.pendiente.toLocaleString());

  const elPhotos = document.getElementById('txtTotalPhotosCount');
  if (elPhotos) {
    elPhotos.innerHTML = `
      <i data-lucide="camera" class="w-3.5 h-3.5"></i>
      <span>${totalPhotos} fotos</span>
    `;
  }

  // Barra de progreso
  const pctTerminados = total > 0 ? ((counts.terminado / total) * 100).toFixed(1) : '0.0';
  setTxt('badgeGlobalPct', `${pctTerminados}% Terminado`);
  setTxt('txtProgress9m', `${terminados9m} / 524 (${((terminados9m / 524) * 100).toFixed(1)}%)`);
  setTxt('txtProgress13m', `${terminados13m} / 131 (${((terminados13m / 131) * 100).toFixed(1)}%)`);

  const setWidth = (id, pct) => {
    const el = document.getElementById(id);
    if (el) el.style.width = `${pct}%`;
  };

  setWidth('barTerminados', (counts.terminado / total) * 100);
  setWidth('barIzado', (counts.izado_sin_solado / total) * 100);
  setWidth('barFaltaSolado', (counts.falta_solado / total) * 100);
  setWidth('barExcavados', (counts.excavado / total) * 100);
  setWidth('barCorte', (counts.corte / total) * 100);

  renderPolesTable();

  // Actualizar reporte modal si está visible
  const modalRep = document.getElementById('modalReports');
  if (modalRep && !modalRep.classList.contains('hidden')) {
    renderReportsView();
  }

  // Actualizar mapa si está abierto
  const modalMap = document.getElementById('modalMap');
  if (modalMap && !modalMap.classList.contains('hidden')) {
    if (currentMapMode === 'canvas') {
      drawCanvasMap();
    } else {
      updateLeafletMarkers();
    }
  }

  if (window.lucide) window.lucide.createIcons();
}

// ==========================================
// RENDERIZADO DE TABLA PADRÓN CON GOOGLE MAPS
// ==========================================
function getFilteredPoles() {
  const searchEl = document.getElementById('inputSearchPole');
  const stageEl = document.getElementById('selectStageFilter');
  const crewEl = document.getElementById('selectCrewFilter');

  const q = searchEl ? searchEl.value.trim().toLowerCase() : '';
  const stage = stageEl ? stageEl.value : 'all';
  const crew = crewEl ? crewEl.value : '';

  return polesState.filter(p => {
    if (activeTypeFilter !== 'all' && p.category !== activeTypeFilter) return false;

    if (q) {
      const match = `${p.id} ${p.name} ${p.shortName} ${p.notes || ''} ${p.crew || ''} ${p.installNotes || ''}`.toLowerCase();
      if (!match.includes(q)) return false;
    }

    if (stage !== 'all' && p.stage !== stage) return false;
    if (crew && p.crew !== crew) return false;

    return true;
  });
}

let currentPolesViewMode = (typeof window !== 'undefined' && window.innerWidth >= 768) ? 'table' : 'cards';

window.switchPolesViewMode = function(mode) {
  currentPolesViewMode = mode;
  const cardsContainer = document.getElementById('containerMobilePolesCards');
  const tableContainer = document.getElementById('containerDesktopPolesTable');
  const btnCards = document.getElementById('btnViewModeCards');
  const btnTable = document.getElementById('btnViewModeTable');

  if (mode === 'cards') {
    if (cardsContainer) cardsContainer.classList.remove('hidden');
    if (tableContainer) tableContainer.classList.add('hidden');
    if (btnCards) btnCards.className = 'px-3 py-1 rounded-lg font-bold text-xs bg-white text-slate-900 shadow-xs transition flex items-center gap-1';
    if (btnTable) btnTable.className = 'px-3 py-1 rounded-lg font-bold text-xs text-slate-600 hover:text-slate-900 transition flex items-center gap-1';
  } else {
    if (cardsContainer) cardsContainer.classList.add('hidden');
    if (tableContainer) tableContainer.classList.remove('hidden');
    if (btnTable) btnTable.className = 'px-3 py-1 rounded-lg font-bold text-xs bg-white text-slate-900 shadow-xs transition flex items-center gap-1';
    if (btnCards) btnCards.className = 'px-3 py-1 rounded-lg font-bold text-xs text-slate-600 hover:text-slate-900 transition flex items-center gap-1';
  }
};

function renderPolesTable() {
  const tbody = document.getElementById('tablePolesBody');
  const cardsContainer = document.getElementById('containerMobilePolesCards');
  const filtered = getFilteredPoles();

  if (tbody) tbody.innerHTML = '';
  if (cardsContainer) cardsContainer.innerHTML = '';

  if (filtered.length === 0) {
    if (tbody) {
      tbody.innerHTML = '<tr><td colspan="7" class="px-4 py-8 text-center text-slate-400 font-medium">No se encontraron postes con los filtros seleccionados</td></tr>';
    }
    if (cardsContainer) {
      cardsContainer.innerHTML = '<div class="p-6 text-center text-slate-400 font-medium bg-white rounded-xl border border-slate-200">No se encontraron postes con los filtros seleccionados</div>';
    }
  }

  filtered.forEach(item => {
    const stageCfg = STAGES_CONFIG[item.stage] || STAGES_CONFIG.pendiente;
    const is13m = item.category === '13m';
    const photosCount = item.photos ? item.photos.length : 0;
    const dateDisplay = item.installedAt 
      ? new Date(item.installedAt).toLocaleDateString('es-ES', { day: '2-digit', month: '2-digit', year: '2-digit' }) 
      : '-';

    // 1. RENDERIZAR FILA PARA TABLA PC
    if (tbody) {
      const tr = document.createElement('tr');
      tr.className = `hover:bg-slate-50 transition border-b border-slate-100 ${item.stage === 'terminado' ? 'bg-emerald-50/20' : ''}`;
      tr.innerHTML = `
        <td class="px-3 py-2.5 font-bold text-slate-800 whitespace-nowrap">
          <div class="flex items-center gap-1.5">
            <span class="w-2 h-2 rounded-full ${stageCfg.dot} shrink-0"></span>
            <span class="text-xs font-bold">${item.name}</span>
            <span class="text-[9px] font-mono px-1 py-0.2 rounded bg-slate-200/80 text-slate-700 font-bold">${item.shortName}</span>
          </div>
        </td>
        <td class="px-3 py-2.5 whitespace-nowrap">
          <span class="inline-flex items-center px-1.5 py-0.5 rounded text-[10px] font-black ${is13m ? 'bg-indigo-100 text-indigo-800 border border-indigo-200' : 'bg-emerald-100 text-emerald-800 border border-emerald-200'}">
            ${is13m ? '📹 13m' : '🏗️ 9m'}
          </span>
        </td>
        <td class="px-3 py-2.5 text-center whitespace-nowrap">
          <a href="${item.googleMapsUrl}" target="_blank" rel="noopener noreferrer" class="inline-flex items-center gap-1 px-2 py-1 text-[10px] font-bold text-blue-700 bg-blue-50 hover:bg-blue-100 border border-blue-200 rounded-lg shadow-2xs transition" title="Abrir ubicación en Google Maps">
            <i data-lucide="navigation" class="w-3 h-3 text-blue-600"></i>
            <span>GPS</span>
          </a>
        </td>
        <td class="px-3 py-2.5 text-center whitespace-nowrap">
          <span class="inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-[10px] font-extrabold ${stageCfg.badgeBg} ${stageCfg.badgeText} border ${stageCfg.border}">
            ${stageCfg.name}
          </span>
        </td>
        <td class="px-3 py-2.5 text-center whitespace-nowrap">
          ${photosCount > 0 
            ? `<button onclick="handleViewFirstPhoto('${item.id}')" class="inline-flex items-center gap-1 px-1.5 py-0.5 rounded-md text-[10px] font-bold bg-indigo-50 text-indigo-700 border border-indigo-200 hover:bg-indigo-100 transition" title="Ver fotos">
                <i data-lucide="image" class="w-3 h-3"></i> ${photosCount}
               </button>` 
            : '<span class="text-slate-300 text-[10px]">-</span>'}
        </td>
        <td class="px-3 py-2.5 text-[10px] text-slate-600 whitespace-nowrap">
          ${item.crew 
            ? `<div><span class="font-bold text-slate-800">${escapeHtml(item.crew)}</span> <span class="text-slate-400">(${dateDisplay})</span></div>` 
            : '<span class="text-slate-300 italic">-</span>'}
        </td>
        <td class="px-3 py-2.5 text-right whitespace-nowrap">
          <button onclick="handleOpenSingleInstallModal('${item.id}')" class="px-2.5 py-1 text-[11px] font-bold bg-emerald-50 hover:bg-emerald-100 text-emerald-800 border border-emerald-300 rounded-lg shadow-2xs transition flex items-center gap-1 ml-auto">
            <i data-lucide="edit" class="w-3 h-3"></i> Info
          </button>
        </td>
      `;
      tbody.appendChild(tr);
    }

    // 2. RENDERIZAR TARJETA ADAPTADA A CELULAR (MOBILE CARD)
    if (cardsContainer) {
      const card = document.createElement('div');
      card.className = `bg-white rounded-xl p-3 border shadow-xs transition space-y-2.5 ${item.stage === 'terminado' ? 'border-emerald-300 bg-emerald-50/10' : 'border-slate-200'}`;
      card.innerHTML = `
        <div class="flex items-center justify-between">
          <div class="flex items-center gap-2">
            <span class="w-3 h-3 rounded-full ${stageCfg.dot} shrink-0 ring-2 ring-slate-100"></span>
            <div>
              <span class="text-sm font-black text-slate-900">${item.name}</span>
              <span class="text-[10px] font-mono font-bold px-1.5 py-0.5 rounded bg-slate-100 text-slate-700 border border-slate-200 ml-1">${item.shortName}</span>
            </div>
          </div>
          <span class="inline-flex items-center px-2 py-0.5 rounded-lg text-[10px] font-black ${is13m ? 'bg-indigo-100 text-indigo-800 border border-indigo-200' : 'bg-emerald-100 text-emerald-800 border border-emerald-200'}">
            ${is13m ? '📹 13m Cámara' : '🏗️ 9m Poste'}
          </span>
        </div>

        <div class="flex items-center justify-between text-xs bg-slate-50/80 p-2 rounded-lg border border-slate-100">
          <span class="inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-[11px] font-black ${stageCfg.badgeBg} ${stageCfg.badgeText} border ${stageCfg.border}">
            ${stageCfg.name}
          </span>
          <div class="text-[11px] text-slate-500 font-medium text-right">
            ${item.crew 
              ? `<span class="font-bold text-slate-700">${escapeHtml(item.crew)}</span> <span class="text-slate-400">(${dateDisplay})</span>` 
              : '<span class="italic text-slate-400">Sin cuadrilla</span>'}
            ${photosCount > 0 ? `<span class="ml-1.5 font-bold text-indigo-600 bg-indigo-50 px-1.5 py-0.5 rounded border border-indigo-200">📸 ${photosCount}</span>` : ''}
          </div>
        </div>

        <div class="grid grid-cols-2 gap-2 pt-0.5">
          <button onclick="handleOpenSingleInstallModal('${item.id}')" class="py-2.5 px-3 text-xs font-black text-white bg-emerald-600 hover:bg-emerald-500 rounded-xl transition flex items-center justify-center gap-1.5 shadow-md shadow-emerald-600/20 active:scale-95">
            <i data-lucide="edit-3" class="w-4 h-4"></i>
            <span>✏️ Llenar / Foto</span>
          </button>
          <a href="${item.googleMapsUrl}" target="_blank" rel="noopener noreferrer" class="py-2.5 px-3 text-xs font-bold text-sky-900 bg-sky-100 hover:bg-sky-200 border border-sky-300 rounded-xl transition flex items-center justify-center gap-1.5 shadow-xs active:scale-95 text-center">
            <i data-lucide="navigation" class="w-4 h-4 text-sky-600"></i>
            <span>📍 Google Maps</span>
          </a>
        </div>
      `;
      cardsContainer.appendChild(card);
    }
  });

  const sumEl = document.getElementById('tablePolesSummary');
  if (sumEl) sumEl.textContent = `Mostrando ${filtered.length} de ${polesState.length}`;

  const filtEl = document.getElementById('txtFilteredSummary');
  if (filtEl) filtEl.textContent = `${filtered.length} puntos`;

  if (window.lucide) window.lucide.createIcons();
}

// ==========================================
// CENTRO DE REPORTES FORMAL DE OBRA
// ==========================================
window.handleOpenReportsModal = function() {
  const modal = document.getElementById('modalReports');
  if (modal) {
    modal.classList.remove('hidden');
    populateReportCrewFilter();
    renderReportsView();
  }
};

window.handleCloseReportsModal = function() {
  const modal = document.getElementById('modalReports');
  if (modal) modal.classList.add('hidden');
};

window.handleReportCheckboxChange = function() {
  // 1. Etapas
  reportMultiFilters.stages.clear();
  ['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente'].forEach(st => {
    const chk = document.getElementById(`chkStage_${st}`);
    if (chk && chk.checked) {
      reportMultiFilters.stages.add(st);
    }
  });

  // 2. Tipos
  reportMultiFilters.types.clear();
  if (document.getElementById('chkType_9m')?.checked) reportMultiFilters.types.add('9m');
  if (document.getElementById('chkType_13m')?.checked) reportMultiFilters.types.add('13m');

  // 3. Fotos
  const photoSel = document.getElementById('repFilterPhotos');
  if (photoSel) {
    reportMultiFilters.photos = photoSel.value;
  }

  renderReportsView();
};

window.handleSelectAllStages = function(selectAll = true) {
  ['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente'].forEach(st => {
    const chk = document.getElementById(`chkStage_${st}`);
    if (chk) chk.checked = selectAll;
  });

  handleReportCheckboxChange();
};

window.handleSelectInProgressStages = function() {
  const inProgress = ['izado_sin_solado', 'falta_solado', 'excavado', 'corte'];
  ['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente'].forEach(st => {
    const chk = document.getElementById(`chkStage_${st}`);
    if (chk) chk.checked = inProgress.includes(st);
  });

  handleReportCheckboxChange();
  showToast('Filtrando: Solo postes en ejecución', 'info');
};

window.handleSelectAllReportOptions = function() {
  // Activar todas las etapas
  ['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente'].forEach(st => {
    const chk = document.getElementById(`chkStage_${st}`);
    if (chk) chk.checked = true;
  });

  // Activar ambos tipos
  const chk9m = document.getElementById('chkType_9m');
  const chk13m = document.getElementById('chkType_13m');
  if (chk9m) chk9m.checked = true;
  if (chk13m) chk13m.checked = true;

  // Activar todas las cuadrillas
  reportMultiFilters.crews = new Set(['ALL']);
  const crewSel = document.getElementById('repFilterCrew');
  if (crewSel) crewSel.value = 'ALL';
  const chkAllCrew = document.getElementById('chkCrew_ALL');
  if (chkAllCrew) chkAllCrew.checked = true;
  document.querySelectorAll('.crew-chk-item').forEach(c => c.checked = true);
  updateCrewSelectionBadge();

  // Fotos
  const photoSel = document.getElementById('repFilterPhotos');
  if (photoSel) photoSel.value = 'all';

  handleReportCheckboxChange();
  showToast('Todas las opciones seleccionadas', 'success');
};

window.handleResetReportFilters = function() {
  handleSelectAllReportOptions();
};

function getReportFilteredPoles() {
  return polesState.filter(p => {
    // Filtro Tipo
    if (!reportMultiFilters.types.has(p.category)) return false;

    // Filtro Etapa
    const st = p.stage || 'pendiente';
    if (!reportMultiFilters.stages.has(st)) return false;

    // Filtro Cuadrillas
    if (!reportMultiFilters.crews.has('ALL')) {
      const crewName = (p.crew || 'Sin Cuadrilla Asignada').trim();
      if (!reportMultiFilters.crews.has(crewName)) return false;
    }

    // Filtro Fotos
    const hasPhotos = p.photos && p.photos.length > 0;
    if (reportMultiFilters.photos === 'with_photos' && !hasPhotos) return false;
    if (reportMultiFilters.photos === 'without_photos' && hasPhotos) return false;

    return true;
  });
}

function renderReportsView() {
  const dateEl = document.getElementById('repGeneratedDate');
  if (dateEl) {
    dateEl.textContent = `Generado: ${new Date().toLocaleDateString('es-ES', { day: '2-digit', month: 'long', year: 'numeric' })} - ${new Date().toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit' })}`;
  }

  const filteredPoles = getReportFilteredPoles();
  const totalScope = filteredPoles.length;
  const totalGlobal = polesState.length; // 655

  const counts = {
    terminado: 0,
    izado_sin_solado: 0,
    falta_solado: 0,
    excavado: 0,
    corte: 0,
    pendiente: 0
  };

  let totalFotos = 0;
  const p9mCounts = { terminado: 0, izado_sin_solado: 0, falta_solado: 0, excavado: 0, corte: 0, pendiente: 0 };
  const p13mCounts = { terminado: 0, izado_sin_solado: 0, falta_solado: 0, excavado: 0, corte: 0, pendiente: 0 };
  const crewStats = {};

  filteredPoles.forEach(p => {
    const st = p.stage || 'pendiente';
    if (counts[st] !== undefined) counts[st]++;
    else counts.pendiente++;

    if (p.category === '9m') p9mCounts[st] = (p9mCounts[st] || 0) + 1;
    if (p.category === '13m') p13mCounts[st] = (p13mCounts[st] || 0) + 1;

    if (p.photos && p.photos.length > 0) totalFotos += p.photos.length;

    // Cuadrillas
    const cName = p.crew ? p.crew.trim() : 'Sin Cuadrilla Asignada';
    if (!crewStats[cName]) {
      crewStats[cName] = { total: 0, p9m: 0, p13m: 0, terminados: 0 };
    }
    crewStats[cName].total++;
    if (p.category === '9m') crewStats[cName].p9m++;
    if (p.category === '13m') crewStats[cName].p13m++;
    if (st === 'terminado') crewStats[cName].terminados++;
  });

  const enProceso = counts.izado_sin_solado + counts.falta_solado + counts.excavado + counts.corte;

  const setTxt = (id, val) => {
    const el = document.getElementById(id);
    if (el) el.textContent = val;
  };

  // KPIs
  setTxt('repTotalSeleccionados', totalScope.toLocaleString());
  setTxt('repPctTotalPadrón', `${((totalScope / totalGlobal) * 100).toFixed(1)}% de 655 totales`);
  setTxt('repTotalTerminados', counts.terminado.toLocaleString());
  setTxt('repPctTerminados', `${totalScope > 0 ? ((counts.terminado / totalScope) * 100).toFixed(1) : '0.0'}%`);
  setTxt('repTotalEnProceso', enProceso.toLocaleString());
  setTxt('repTotalFotos', totalFotos.toLocaleString());

  const badgeCount = document.getElementById('repFilteredCountBadge');
  if (badgeCount) {
    badgeCount.textContent = `${totalScope} punto(s) encontrado(s)`;
  }

  // 1. Tabla de Etapas del Subconjunto
  const tableStages = document.getElementById('repTableStagesBody');
  if (tableStages) {
    tableStages.innerHTML = '';
    const stageKeys = ['terminado', 'izado_sin_solado', 'falta_solado', 'excavado', 'corte', 'pendiente'];

    let sum9m = 0, sum13m = 0;

    stageKeys.forEach(stKey => {
      const cfg = STAGES_CONFIG[stKey];
      const countTotal = counts[stKey] || 0;
      const count9m = p9mCounts[stKey] || 0;
      const count13m = p13mCounts[stKey] || 0;
      sum9m += count9m;
      sum13m += count13m;
      const pct = totalScope > 0 ? ((countTotal / totalScope) * 100).toFixed(1) : '0.0';

      const tr = document.createElement('tr');
      tr.className = stKey === 'terminado' ? 'bg-emerald-50/40 font-bold' : '';
      tr.innerHTML = `
        <td class="px-4 py-2 font-bold flex items-center gap-2">
          <span class="w-2.5 h-2.5 rounded-full ${cfg.dot}"></span>
          <span>${cfg.name}</span>
        </td>
        <td class="px-4 py-2 text-center font-mono font-bold">${count9m}</td>
        <td class="px-4 py-2 text-center font-mono font-bold">${count13m}</td>
        <td class="px-4 py-2 text-center font-mono font-extrabold text-slate-800">${countTotal}</td>
        <td class="px-4 py-2 text-right font-bold">${pct}%</td>
      `;
      tableStages.appendChild(tr);
    });

    // Fila Total
    const trTotal = document.createElement('tr');
    trTotal.className = 'bg-slate-100 font-black text-slate-900 border-t-2 border-slate-300';
    trTotal.innerHTML = `
      <td class="px-4 py-2.5">TOTAL SELECCIONADO</td>
      <td class="px-4 py-2.5 text-center font-mono">${sum9m}</td>
      <td class="px-4 py-2.5 text-center font-mono">${sum13m}</td>
      <td class="px-4 py-2.5 text-center font-mono text-base">${totalScope}</td>
      <td class="px-4 py-2.5 text-right">100.0%</td>
    `;
    tableStages.appendChild(trTotal);
  }

  // 2. Listado Detallado Individual de Puntos Filtrados
  const tableFilteredList = document.getElementById('repTableFilteredListBody');
  if (tableFilteredList) {
    tableFilteredList.innerHTML = '';

    if (filteredPoles.length === 0) {
      tableFilteredList.innerHTML = `
        <tr>
          <td colspan="7" class="px-4 py-6 text-center text-slate-400">
            <div class="flex flex-col items-center justify-center gap-1">
              <i data-lucide="info" class="w-5 h-5 text-slate-400"></i>
              <span class="text-xs font-semibold">No hay postes o cámaras que coincidan con los filtros seleccionados</span>
            </div>
          </td>
        </tr>
      `;
    } else {
      filteredPoles.forEach((item, idx) => {
        const stageCfg = STAGES_CONFIG[item.stage] || STAGES_CONFIG.pendiente;
        const is13m = item.category === '13m';
        const photoCount = item.photos ? item.photos.length : 0;
        const dateDisplay = item.installedAt
          ? new Date(item.installedAt).toLocaleDateString('es-ES', { day: '2-digit', month: '2-digit', year: '2-digit' })
          : '-';

        const tr = document.createElement('tr');
        tr.className = `hover:bg-slate-50 transition border-b border-slate-100 ${item.stage === 'terminado' ? 'bg-emerald-50/20' : ''}`;
        tr.innerHTML = `
          <td class="px-2.5 py-2 text-center font-mono font-bold text-slate-400 text-[11px] whitespace-nowrap">
            ${idx + 1}
          </td>
          <td class="px-3 py-2 font-bold text-slate-800 whitespace-nowrap">
            <div class="flex items-center gap-1.5">
              <span class="w-2 h-2 rounded-full ${stageCfg.dot} shrink-0"></span>
              <span class="font-bold">${item.name}</span>
            </div>
          </td>
          <td class="px-2.5 py-2 text-center whitespace-nowrap">
            <span class="text-[10px] font-mono px-1.5 py-0.5 rounded bg-slate-200 text-slate-800 font-black">${item.shortName}</span>
          </td>
          <td class="px-3 py-2 whitespace-nowrap">
            <span class="inline-flex items-center px-1.5 py-0.5 rounded text-[9px] font-bold ${is13m ? 'bg-indigo-100 text-indigo-800 border border-indigo-200' : 'bg-emerald-100 text-emerald-800 border border-emerald-200'}">
              ${is13m ? '📹 13m' : '🏗️ 9m'}
            </span>
          </td>
          <td class="px-3 py-2 whitespace-nowrap font-mono text-[11px] font-bold text-slate-800">
            ${item.x ? item.x.toFixed(2) : '-'}
          </td>
          <td class="px-3 py-2 whitespace-nowrap font-mono text-[11px] font-bold text-slate-800">
            ${item.y ? item.y.toFixed(2) : '-'}
          </td>
          <td class="px-3 py-2 text-center whitespace-nowrap">
            <span class="inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-[9px] font-extrabold ${stageCfg.badgeBg} ${stageCfg.badgeText} border ${stageCfg.border}">
              ${stageCfg.name}
            </span>
          </td>
          <td class="px-3 py-2 text-center text-[11px] font-medium text-slate-700 whitespace-nowrap">
            ${dateDisplay}
          </td>
          <td class="px-3 py-2 text-right whitespace-nowrap">
            <div class="inline-flex items-center gap-1">
              ${photoCount > 0 
                ? `<button onclick="handleViewFirstPhoto('${item.id}')" class="inline-flex items-center gap-0.5 px-1.5 py-0.5 rounded text-[10px] font-bold bg-indigo-50 text-indigo-700 border border-indigo-200 hover:bg-indigo-100 transition" title="Ver foto">
                    <i data-lucide="image" class="w-3 h-3"></i> ${photoCount}
                   </button>` 
                : ''}
              <button onclick="handleOpenSingleFromReport('${item.id}')" class="px-2 py-0.5 text-[10px] font-bold text-slate-700 bg-slate-100 hover:bg-slate-200 border border-slate-200 rounded-md transition" title="Editar este poste">
                ✏️ Editar
              </button>
            </div>
          </td>
        `;
        tableFilteredList.appendChild(tr);
      });
    }
  }

  // 3. Tabla de Cuadrillas
  const tableCrews = document.getElementById('repTableCrewsBody');
  if (tableCrews) {
    tableCrews.innerHTML = '';
    const crewEntries = Object.entries(crewStats);

    if (crewEntries.length === 0) {
      tableCrews.innerHTML = '<tr><td colspan="5" class="px-4 py-3 text-center text-slate-400">Sin registros de cuadrillas en esta selección</td></tr>';
    } else {
      crewEntries.forEach(([cName, st]) => {
        const tr = document.createElement('tr');
        tr.innerHTML = `
          <td class="px-4 py-2 font-bold text-slate-800">${escapeHtml(cName)}</td>
          <td class="px-4 py-2 text-center font-mono">${st.p9m}</td>
          <td class="px-4 py-2 text-center font-mono">${st.p13m}</td>
          <td class="px-4 py-2 text-center font-mono font-bold text-emerald-700">${st.terminados}</td>
          <td class="px-4 py-2 text-right font-bold">${st.total}</td>
        `;
        tableCrews.appendChild(tr);
      });
    }
  }

  if (window.lucide) window.lucide.createIcons();
}

window.handleOpenSingleFromReport = function(poleId) {
  handleCloseReportsModal();
  handleOpenSingleInstallModal(poleId);
};

// ==========================================
// MODAL DE DETALLE Y GOOGLE MAPS GPS
// ==========================================
window.handleOpenSingleInstallModal = function(id) {
  const index = polesState.findIndex(p => p.id === id);
  if (index === -1) return;

  currentOpenPoleIndex = index;
  populateModalData(polesState[index]);
  const modal = document.getElementById('modalSingleInstall');
  if (modal) modal.classList.remove('hidden');
};

window.handleCloseSingleModal = function() {
  const modal = document.getElementById('modalSingleInstall');
  if (modal) modal.classList.add('hidden');
};

function populateModalData(pole) {
  document.getElementById('singlePoleId').value = pole.id;
  document.getElementById('singleModalTitle').textContent = pole.name;
  document.getElementById('singleModalShortName').textContent = pole.shortName;
  document.getElementById('singleModalSubtitle').textContent = `UTM Este: ${pole.x.toFixed(2)} | Norte: ${pole.y.toFixed(2)}`;
  
  // GPS Google Maps enlace
  document.getElementById('txtModalGpsCoords').textContent = `Lat: ${pole.lat.toFixed(5)}° | Lng: ${pole.lng.toFixed(5)}°`;
  document.getElementById('btnOpenGoogleMapsUrl').href = pole.googleMapsUrl;

  // Badge de tipo (9m vs 13m)
  const is13m = pole.category === '13m';
  const badge = document.getElementById('badgeModalPoleType');
  if (badge) {
    if (is13m) {
      badge.className = 'p-1.5 rounded-xl text-xs font-black flex items-center gap-1 bg-indigo-600 text-white shadow-xs';
      badge.innerHTML = '<i data-lucide="video" class="w-3.5 h-3.5"></i> 📹 13m Cámara';
    } else {
      badge.className = 'p-1.5 rounded-xl text-xs font-black flex items-center gap-1 bg-emerald-600 text-white shadow-xs';
      badge.innerHTML = '<i data-lucide="tower-control" class="w-3.5 h-3.5"></i> 🏗️ 9 Metros';
    }
  }

  document.getElementById('txtPoleOrderNumber').textContent = `${pole.orderIndex}/${polesState.length}`;

  const activeStage = pole.stage || 'pendiente';
  document.getElementById('singleStage').value = activeStage;
  highlightStageButton(activeStage);

  document.getElementById('singleCrew').value = pole.crew || '';
  if (pole.installedAt) {
    document.getElementById('singleDatetime').value = pole.installedAt.slice(0, 10);
  } else {
    document.getElementById('singleDatetime').value = new Date().toISOString().slice(0, 10);
  }
  
  document.getElementById('singleNotes').value = pole.installNotes || '';

  renderPolePhotos(pole);
  if (window.lucide) window.lucide.createIcons();
}

function highlightStageButton(stage) {
  document.querySelectorAll('.stage-btn').forEach(btn => {
    if (btn.dataset.stage === stage) {
      btn.classList.add('selected');
    } else {
      btn.classList.remove('selected');
    }
  });
}

document.querySelectorAll('.stage-btn').forEach(btn => {
  btn.addEventListener('click', function() {
    const stage = this.dataset.stage;
    document.getElementById('singleStage').value = stage;
    highlightStageButton(stage);
  });
});

window.handlePrevPole = function() {
  if (currentOpenPoleIndex > 0) {
    currentOpenPoleIndex--;
    populateModalData(polesState[currentOpenPoleIndex]);
  } else {
    showToast('Inicio del padrón alcanzado', 'info');
  }
};

window.handleNextPole = function() {
  if (currentOpenPoleIndex < polesState.length - 1) {
    currentOpenPoleIndex++;
    populateModalData(polesState[currentOpenPoleIndex]);
  } else {
    showToast('Fin del padrón alcanzado', 'info');
  }
};

window.handleSaveAndNextPole = function() {
  handleSaveSingleInstall(null, true);
};

function handleSaveSingleInstall(e, shouldMoveNext = false) {
  if (e) e.preventDefault();

  const id = document.getElementById('singlePoleId').value;
  const stage = document.getElementById('singleStage').value;
  const crew = document.getElementById('singleCrew').value.trim();
  const datetime = document.getElementById('singleDatetime').value;
  const notes = document.getElementById('singleNotes').value.trim();

  const pole = polesState.find(p => p.id === id);
  if (pole) {
    pole.stage = stage;
    pole.crew = crew;
    pole.installedAt = datetime;
    pole.installNotes = notes;

    savePolesToStorage();
    populateCrewFilters();
    updateDashboard();

    // Auto-sincronización instantánea con la nube en segundo plano
    autoSyncPushToCloud();

    showToast(`✅ ${pole.name} (${pole.shortName}) guardado como: ${STAGES_CONFIG[stage].name}`, 'success');

    if (shouldMoveNext) {
      if (currentOpenPoleIndex < polesState.length - 1) {
        currentOpenPoleIndex++;
        populateModalData(polesState[currentOpenPoleIndex]);
      } else {
        handleCloseSingleModal();
        showToast('¡Has completado el último poste del padrón!', 'success');
      }
    } else {
      handleCloseSingleModal();
    }
  }
}

window.handleClearCurrentPole = function() {
  const id = document.getElementById('singlePoleId').value;
  const pole = polesState.find(p => p.id === id);
  if (!pole) return;

  const hasData = (pole.stage && pole.stage !== 'pendiente') || pole.crew || pole.installedAt || pole.installNotes || (pole.photos && pole.photos.length > 0);
  
  if (!hasData) {
    showToast('Este punto ya se encuentra en estado inicial (Sin datos ingresados)', 'info');
    return;
  }

  const photoMsg = pole.photos && pole.photos.length > 0 ? `\n• Se eliminarán ${pole.photos.length} fotografía(s) adjunta(s)` : '';
  const confirmMsg = `⚠️ ¿Deseas eliminar y limpiar toda la información ingresada en "${pole.name} (${pole.shortName})"?\n\n• Volverá a estado "Sin Iniciar"\n• Se limpiarán la cuadrilla, fecha de registro y observaciones${photoMsg}`;

  if (confirm(confirmMsg)) {
    pole.stage = 'pendiente';
    pole.crew = '';
    pole.installedAt = '';
    pole.installNotes = '';
    pole.photos = [];

    savePolesToStorage();
    populateCrewFilters();
    updateDashboard();
    populateModalData(pole);

    // Auto-sincronización instantánea con la nube en segundo plano
    autoSyncPushToCloud();

    showToast(`🗑️ Datos de ${pole.name} eliminados y restablecidos`, 'info');
  }
};

// Fotos
function renderPolePhotos(pole) {
  const grid = document.getElementById('polePhotosGrid');
  const txtNo = document.getElementById('txtNoPhotos');
  if (!grid) return;

  grid.innerHTML = '';
  const photos = pole.photos || [];

  if (photos.length === 0) {
    if (txtNo) {
      txtNo.classList.remove('hidden');
      grid.appendChild(txtNo);
    }
    return;
  }

  if (txtNo) txtNo.classList.add('hidden');

  photos.forEach((photo, idx) => {
    const div = document.createElement('div');
    div.className = 'photo-thumb group';
    div.innerHTML = `
      <img src="${photo.dataUrl}" alt="Foto ${idx + 1}" onclick="handleOpenPhotoViewer('${pole.id}', ${idx})">
      <button type="button" onclick="handleDeletePhoto('${pole.id}', ${idx})" class="btn-delete-photo" title="Eliminar foto">
        <i data-lucide="x" class="w-3 h-3"></i>
      </button>
    `;
    grid.appendChild(div);
  });

  if (window.lucide) window.lucide.createIcons();
}

const inputPhoto = document.getElementById('inputPolePhoto');
if (inputPhoto) {
  inputPhoto.addEventListener('change', function(e) {
    const file = e.target.files[0];
    if (!file) return;

    const poleId = document.getElementById('singlePoleId').value;
    const pole = polesState.find(p => p.id === poleId);
    if (!pole) return;

    const reader = new FileReader();
    reader.onload = function(evt) {
      const img = new Image();
      img.onload = function() {
        const maxDim = 800;
        let width = img.width;
        let height = img.height;

        if (width > height && width > maxDim) {
          height *= maxDim / width;
          width = maxDim;
        } else if (height > maxDim) {
          width *= maxDim / height;
          height = maxDim;
        }

        const canvas = document.createElement('canvas');
        canvas.width = width;
        canvas.height = height;
        const ctx = canvas.getContext('2d');
        ctx.drawImage(img, 0, 0, width, height);

        const compressedBase64 = canvas.toDataURL('image/jpeg', 0.75);

        if (!pole.photos) pole.photos = [];
        pole.photos.push({
          id: 'photo_' + Date.now(),
          dataUrl: compressedBase64,
          date: new Date().toISOString()
        });

        renderPolePhotos(pole);
        savePolesToStorage();
        showToast('📸 Foto adjunta guardada', 'success');
      };
      img.src = evt.target.result;
    };
    reader.readAsDataURL(file);
  });
}

window.handleDeletePhoto = function(poleId, photoIndex) {
  const pole = polesState.find(p => p.id === poleId);
  if (!pole || !pole.photos) return;

  if (confirm('¿Eliminar esta fotografía?')) {
    pole.photos.splice(photoIndex, 1);
    renderPolePhotos(pole);
    savePolesToStorage();
    showToast('Foto eliminada', 'info');
  }
};

window.handleViewFirstPhoto = function(poleId) {
  const pole = polesState.find(p => p.id === poleId);
  if (pole && pole.photos && pole.photos.length > 0) {
    handleOpenPhotoViewer(poleId, 0);
  }
};

window.handleOpenPhotoViewer = function(poleId, photoIndex) {
  const pole = polesState.find(p => p.id === poleId);
  if (!pole || !pole.photos || !pole.photos[photoIndex]) return;

  const photo = pole.photos[photoIndex];
  document.getElementById('imgViewerTarget').src = photo.dataUrl;
  document.getElementById('txtViewerCaption').textContent = `${pole.name} (${pole.shortName}) • Foto ${photoIndex + 1} de ${pole.photos.length} • ${new Date(photo.date).toLocaleString('es-ES')}`;
  document.getElementById('modalPhotoViewer').classList.remove('hidden');
};

window.handleClosePhotoViewer = function() {
  document.getElementById('modalPhotoViewer').classList.add('hidden');
};

// ==========================================
// MODAL: PLANO GEOESPACIAL Y MAPA SATELITAL
// ==========================================
window.handleOpenMapModal = function() {
  const modal = document.getElementById('modalMap');
  if (modal) {
    modal.classList.remove('hidden');
    setTimeout(() => {
      initOrUpdateLeafletMap();
    }, 150);
  }
};

window.handleCloseMapModal = function() {
  const modal = document.getElementById('modalMap');
  if (modal) modal.classList.add('hidden');
};

function initOrUpdateLeafletMap() {
  if (typeof L === 'undefined') {
    setMapLayer('canvas');
    return;
  }

  const container = document.getElementById('leafletMapContainer');
  if (!container) return;

  if (!leafletMap) {
    leafletMap = L.map('leafletMapContainer', {
      zoomControl: true,
      attributionControl: false
    });

    leafletTileSatellite = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', {
      maxZoom: 19
    });

    leafletTileStreets = L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
      maxZoom: 19
    });

    leafletTileSatellite.addTo(leafletMap);
    leafletMarkersLayer = L.layerGroup().addTo(leafletMap);
  }

  setTimeout(() => {
    leafletMap.invalidateSize();
    updateLeafletMarkers();
  }, 100);
}

function updateLeafletMarkers() {
  if (!leafletMap || !leafletMarkersLayer) return;

  leafletMarkersLayer.clearLayers();
  const validPoles = polesState.filter(p => p.lat && p.lng);

  if (validPoles.length === 0) return;

  const latLngs = [];

  validPoles.forEach(p => {
    const is13m = p.category === '13m';
    const cfg = STAGES_CONFIG[p.stage] || STAGES_CONFIG.pendiente;
    const radius = is13m ? 6 : 5;
    const isTerminado = p.stage === 'terminado';

    const marker = L.circleMarker([p.lat, p.lng], {
      radius: isTerminado ? radius + 1.5 : radius,
      color: isTerminado ? '#10b981' : '#ffffff',
      weight: isTerminado ? 2.5 : 1,
      fillColor: cfg.color,
      fillOpacity: 0.95
    });

    if (mapLabelMode !== 'none') {
      const labelText = mapLabelMode === 'short' ? p.shortName : p.name;
      marker.bindTooltip(labelText, {
        permanent: true,
        direction: 'right',
        offset: [radius + 2, 0],
        className: 'pole-map-label'
      });
    }

    const popupContent = `
      <div class="text-xs space-y-1.5 p-1 font-sans">
        <div class="flex items-center justify-between gap-2 border-b border-slate-700 pb-1">
          <strong class="text-white text-sm">${p.name} (${p.shortName})</strong>
          <span class="text-[10px] font-bold px-1.5 py-0.2 rounded ${cfg.badgeBg} ${cfg.badgeText}">${cfg.name}</span>
        </div>
        <div class="text-[10px] text-slate-300 font-mono">UTM: E ${p.x.toFixed(1)} | N ${p.y.toFixed(1)}</div>
        <div class="text-[10px] text-blue-300 font-mono">GPS: ${p.lat.toFixed(5)}°, ${p.lng.toFixed(5)}°</div>
        <div class="text-[10px] text-indigo-300 font-semibold">${is13m ? '📹 13m (Cámara)' : '🏗️ 9 Metros'}</div>
        ${p.photos && p.photos.length > 0 ? `<div class="text-[10px] text-emerald-400 font-bold">📸 ${p.photos.length} foto(s)</div>` : ''}
        ${p.crew ? `<div class="text-[10px] text-slate-400">Cuadrilla: ${escapeHtml(p.crew)}</div>` : ''}
        <div class="flex gap-1.5 pt-1 border-t border-slate-700">
          <a href="${p.googleMapsUrl}" target="_blank" rel="noopener noreferrer" class="flex-1 px-2 py-1 bg-blue-600 hover:bg-blue-500 text-white rounded-lg text-[10px] font-bold text-center flex items-center justify-center gap-1">
            🗺️ Google Maps
          </a>
          <button onclick="handleOpenSingleInstallModal('${p.id}')" class="px-2 py-1 bg-slate-700 hover:bg-slate-600 text-white rounded-lg text-[10px] font-bold">
            ✏️ Editar
          </button>
        </div>
      </div>
    `;

    marker.bindPopup(popupContent, { maxWidth: 260 });
    leafletMarkersLayer.addLayer(marker);
    latLngs.push([p.lat, p.lng]);
  });

  if (latLngs.length > 0) {
    leafletMap.fitBounds(L.latLngBounds(latLngs), { padding: [30, 30] });
  }
}

window.setMapLayer = function(layer) {
  currentMapMode = layer;

  const btnSat = document.getElementById('btnMapLayerSatellite');
  const btnStr = document.getElementById('btnMapLayerStreets');
  const btnCan = document.getElementById('btnMapLayerCanvas');

  const activeClass = 'px-2 py-1 rounded bg-sky-600 text-white font-bold transition flex items-center gap-1';
  const inactiveClass = 'px-2 py-1 rounded text-slate-300 hover:text-white transition flex items-center gap-1';

  if (btnSat) btnSat.className = layer === 'satellite' ? activeClass : inactiveClass;
  if (btnStr) btnStr.className = layer === 'streets' ? activeClass : inactiveClass;
  if (btnCan) btnCan.className = layer === 'canvas' ? activeClass : inactiveClass;

  const leafContainer = document.getElementById('leafletMapContainer');
  const canvasContainer = document.getElementById('canvasMapContainer');

  if (layer === 'canvas') {
    if (leafContainer) leafContainer.classList.add('hidden');
    if (canvasContainer) canvasContainer.classList.remove('hidden');
    setTimeout(drawCanvasMap, 50);
  } else {
    if (canvasContainer) canvasContainer.classList.add('hidden');
    if (leafContainer) leafContainer.classList.remove('hidden');

    if (!leafletMap) {
      initOrUpdateLeafletMap();
    } else {
      if (layer === 'satellite') {
        if (leafletMap.hasLayer(leafletTileStreets)) leafletMap.removeLayer(leafletTileStreets);
        if (!leafletMap.hasLayer(leafletTileSatellite)) leafletTileSatellite.addTo(leafletMap);
      } else {
        if (leafletMap.hasLayer(leafletTileSatellite)) leafletMap.removeLayer(leafletTileSatellite);
        if (!leafletMap.hasLayer(leafletTileStreets)) leafletTileStreets.addTo(leafletMap);
      }
      leafletMap.invalidateSize();
    }
  }
};

window.setMapLabelMode = function(mode) {
  mapLabelMode = mode;
  const btnShort = document.getElementById('btnLabelModeShort');
  const btnFull = document.getElementById('btnLabelModeFull');
  const btnNone = document.getElementById('btnLabelModeNone');

  const activeClass = 'px-2 py-0.5 rounded bg-indigo-600 text-white font-bold transition';
  const inactiveClass = 'px-2 py-0.5 rounded text-slate-400 hover:text-white transition font-medium';

  if (btnShort) btnShort.className = mode === 'short' ? activeClass : inactiveClass;
  if (btnFull) btnFull.className = mode === 'full' ? activeClass : inactiveClass;
  if (btnNone) btnNone.className = mode === 'none' ? activeClass : inactiveClass;

  if (currentMapMode === 'canvas') {
    drawCanvasMap();
  } else {
    updateLeafletMarkers();
  }
};

// ==========================================
// PLANO CANVAS UTM 2D (RESPALDO / ALTERNATIVO)
// ==========================================
function setupCanvasMap() {
  const canvas = document.getElementById('utmCanvas');
  if (!canvas) return;

  canvas.addEventListener('mousedown', (e) => {
    isDraggingMap = true;
    startDragX = e.clientX - mapOffsetX;
    startDragY = e.clientY - mapOffsetY;
  });

  window.addEventListener('mouseup', () => isDraggingMap = false);

  canvas.addEventListener('mousemove', (e) => {
    const rect = canvas.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    if (isDraggingMap) {
      mapOffsetX = e.clientX - startDragX;
      mapOffsetY = e.clientY - startDragY;
      drawCanvasMap();
      return;
    }

    checkCanvasMapHover(mouseX, mouseY);
  });

  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    const zoomFactor = e.deltaY < 0 ? 1.2 : 0.8;
    mapZoom = Math.max(0.4, Math.min(22, mapZoom * zoomFactor));
    drawCanvasMap();
  });

  canvas.addEventListener('click', () => {
    if (hoveredPole) {
      handleOpenSingleInstallModal(hoveredPole.id);
    }
  });

  canvas.addEventListener('touchstart', (e) => {
    if (e.touches.length === 1) {
      isDraggingMap = true;
      startDragX = e.touches[0].clientX - mapOffsetX;
      startDragY = e.touches[0].clientY - mapOffsetY;
    } else if (e.touches.length === 2) {
      isDraggingMap = false;
      touchStartDist = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
      touchStartZoom = mapZoom;
    }
  }, { passive: true });

  canvas.addEventListener('touchmove', (e) => {
    if (e.touches.length === 1 && isDraggingMap) {
      mapOffsetX = e.touches[0].clientX - startDragX;
      mapOffsetY = e.touches[0].clientY - startDragY;
      drawCanvasMap();
    } else if (e.touches.length === 2 && touchStartDist > 0) {
      const currentDist = Math.hypot(
        e.touches[0].clientX - e.touches[1].clientX,
        e.touches[0].clientY - e.touches[1].clientY
      );
      const scale = currentDist / touchStartDist;
      mapZoom = Math.max(0.4, Math.min(22, touchStartZoom * scale));
      drawCanvasMap();
    }
  }, { passive: true });

  canvas.addEventListener('touchend', (e) => {
    isDraggingMap = false;
    touchStartDist = 0;
    if (e.changedTouches.length === 1) {
      const rect = canvas.getBoundingClientRect();
      const touchX = e.changedTouches[0].clientX - rect.left;
      const touchY = e.changedTouches[0].clientY - rect.top;
      checkCanvasMapHover(touchX, touchY);
      if (hoveredPole) {
        handleOpenSingleInstallModal(hoveredPole.id);
      }
    }
  });

  const btnIn = document.getElementById('btnZoomIn');
  const btnOut = document.getElementById('btnZoomOut');
  const btnReset = document.getElementById('btnResetMap');

  if (btnIn) btnIn.addEventListener('click', () => { mapZoom = Math.min(22, mapZoom * 1.35); drawCanvasMap(); });
  if (btnOut) btnOut.addEventListener('click', () => { mapZoom = Math.max(0.4, mapZoom * 0.75); drawCanvasMap(); });
  if (btnReset) btnReset.addEventListener('click', () => { mapZoom = 1; mapOffsetX = 0; mapOffsetY = 0; drawCanvasMap(); });
}

function drawCanvasMap() {
  const canvas = document.getElementById('utmCanvas');
  const container = document.getElementById('canvasMapContainer');
  if (!canvas || !container) return;

  const ctx = canvas.getContext('2d');
  canvas.width = container.clientWidth || 800;
  canvas.height = container.clientHeight || 500;

  const w = canvas.width;
  const h = canvas.height;

  ctx.clearRect(0, 0, w, h);

  const minX = 727300, maxX = 731050;
  const minY = 8490450, maxY = 8493000;
  const rangeX = maxX - minX;
  const rangeY = maxY - minY;

  const padding = 40;
  const scaleX = (w - padding * 2) / rangeX;
  const scaleY = (h - padding * 2) / rangeY;
  const baseScale = Math.min(scaleX, scaleY);

  ctx.save();
  ctx.translate(w / 2 + mapOffsetX, h / 2 + mapOffsetY);
  ctx.scale(mapZoom, mapZoom);
  ctx.translate(-w / 2, -h / 2);

  ctx.strokeStyle = '#1e293b';
  ctx.lineWidth = 1 / mapZoom;
  for (let x = minX; x <= maxX; x += 500) {
    const px = padding + (x - minX) * baseScale;
    ctx.beginPath();
    ctx.moveTo(px, 0);
    ctx.lineTo(px, h);
    ctx.stroke();
  }
  for (let y = minY; y <= maxY; y += 500) {
    const py = h - (padding + (y - minY) * baseScale);
    ctx.beginPath();
    ctx.moveTo(0, py);
    ctx.lineTo(w, py);
    ctx.stroke();
  }

  polesState.forEach(p => {
    if (!p.x || !p.y) return;
    const px = padding + (p.x - minX) * baseScale;
    const py = h - (padding + (p.y - minY) * baseScale);

    p._screenX = px;
    p._screenY = py;

    const st = p.stage || 'pendiente';
    const cfg = STAGES_CONFIG[st] || STAGES_CONFIG.pendiente;
    const is13m = p.category === '13m';
    const radius = is13m ? 3.8 : 2.8;

    if (st === 'terminado') {
      ctx.beginPath();
      ctx.arc(px, py, radius + 2.5, 0, Math.PI * 2);
      ctx.fillStyle = 'rgba(16, 185, 129, 0.45)';
      ctx.fill();
    }

    ctx.beginPath();
    ctx.arc(px, py, radius, 0, Math.PI * 2);
    ctx.fillStyle = cfg.color;
    ctx.fill();

    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth = 0.7;
    ctx.stroke();

    if (mapLabelMode !== 'none') {
      const labelText = mapLabelMode === 'short' ? p.shortName : p.name;
      const fontSize = Math.max(6.5, Math.min(9, 7.5 * Math.sqrt(mapZoom)));
      ctx.font = `bold ${fontSize}px sans-serif`;

      ctx.fillStyle = '#020617';
      ctx.fillText(labelText, px + radius + 2, py + 2.5);

      if (st === 'terminado') ctx.fillStyle = '#6ee7b7';
      else if (is13m) ctx.fillStyle = '#c7d2fe';
      else ctx.fillStyle = '#f8fafc';

      ctx.fillText(labelText, px + radius + 2, py + 2.5);
    }
  });

  ctx.restore();
}

function checkCanvasMapHover(mouseX, mouseY) {
  const canvas = document.getElementById('utmCanvas');
  const tooltip = document.getElementById('mapTooltip');
  if (!canvas || !tooltip) return;

  const w = canvas.width;
  const h = canvas.height;

  let found = null;
  polesState.forEach(p => {
    if (p._screenX === undefined) return;

    const transX = (p._screenX - w / 2) * mapZoom + w / 2 + mapOffsetX;
    const transY = (p._screenY - h / 2) * mapZoom + h / 2 + mapOffsetY;

    const dist = Math.hypot(transX - mouseX, transY - mouseY);
    if (dist < 10) found = p;
  });

  hoveredPole = found;
  if (found) {
    const stageCfg = STAGES_CONFIG[found.stage] || STAGES_CONFIG.pendiente;
    const photoCount = found.photos ? found.photos.length : 0;

    tooltip.classList.remove('hidden');
    tooltip.style.left = `${Math.min(w - 220, mouseX + 12)}px`;
    tooltip.style.top = `${Math.min(h - 140, mouseY + 12)}px`;
    tooltip.innerHTML = `
      <div class="font-black text-xs text-white flex items-center justify-between gap-1">
        <span>${found.name} (${found.shortName})</span>
        <span class="text-[9px] font-bold px-1.5 py-0.2 rounded ${stageCfg.badgeBg} ${stageCfg.badgeText}">${stageCfg.name}</span>
      </div>
      <div class="text-[10px] text-slate-300 font-mono mt-0.5">UTM: E ${found.x.toFixed(1)} | N ${found.y.toFixed(1)}</div>
      <div class="text-[10px] text-blue-300 font-mono">GPS: ${found.lat.toFixed(5)}, ${found.lng.toFixed(5)}</div>
      ${photoCount > 0 ? `<div class="text-[10px] text-emerald-400 font-bold mt-0.5">📸 ${photoCount} foto(s)</div>` : ''}
      <div class="flex items-center gap-1 mt-1.5 pt-1 border-t border-slate-700">
        <a href="${found.googleMapsUrl}" target="_blank" rel="noopener noreferrer" class="px-2 py-0.5 bg-blue-600 hover:bg-blue-500 text-white rounded text-[10px] font-bold flex items-center gap-1">
          <i data-lucide="navigation" class="w-3 h-3"></i> Google Maps
        </a>
        <button onclick="handleOpenSingleInstallModal('${found.id}')" class="px-2 py-0.5 bg-slate-700 hover:bg-slate-600 text-white rounded text-[10px] font-bold">
          Editar
        </button>
      </div>
    `;
    if (window.lucide) window.lucide.createIcons();
    canvas.style.cursor = 'pointer';
  } else {
    tooltip.classList.add('hidden');
    canvas.style.cursor = 'crosshair';
  }
}

// ==========================================
// MODAL: ACTUALIZACIÓN POR RANGO / LOTE
// ==========================================
window.handleOpenBatchModal = function() {
  const modal = document.getElementById('modalBatchInstall');
  const dateInput = document.getElementById('batchDatetime');
  if (dateInput) dateInput.value = new Date().toISOString().slice(0, 10);
  updateBatchCountPreview();
  if (modal) modal.classList.remove('hidden');
};

window.handleCloseBatchModal = function() {
  const modal = document.getElementById('modalBatchInstall');
  if (modal) modal.classList.add('hidden');
};

function updateBatchCountPreview() {
  const fromEl = document.getElementById('batchFromNum');
  const toEl = document.getElementById('batchToNum');
  const typeEl = document.querySelector('input[name="batchType"]:checked');
  const countEl = document.getElementById('txtBatchCount');

  const fromNum = fromEl ? parseInt(fromEl.value, 10) || 1 : 1;
  const toNum = toEl ? parseInt(toEl.value, 10) || 1 : 1;
  const type = typeEl ? typeEl.value : '9m';

  const max = type === '9m' ? 524 : 131;
  const count = Math.max(0, Math.min(toNum, max) - Math.max(1, fromNum) + 1);
  if (countEl) countEl.textContent = count;
}

function handleSaveBatchInstall(e) {
  e.preventDefault();

  const type = document.querySelector('input[name="batchType"]:checked').value;
  const fromNum = parseInt(document.getElementById('batchFromNum').value, 10);
  const toNum = parseInt(document.getElementById('batchToNum').value, 10);
  const stage = document.getElementById('batchStage').value;
  const crew = document.getElementById('batchCrew').value.trim();
  const date = document.getElementById('batchDatetime').value;

  if (isNaN(fromNum) || isNaN(toNum) || fromNum > toNum) {
    showToast('El rango de números es inválido', 'error');
    return;
  }

  let updatedCount = 0;
  polesState.forEach(pole => {
    if (pole.category === type && pole.orderIndex >= fromNum && pole.orderIndex <= toNum) {
      pole.stage = stage;
      if (crew) pole.crew = crew;
      if (date) pole.installedAt = date;
      updatedCount++;
    }
  });

  savePolesToStorage();
  populateCrewFilters();
  updateDashboard();
  handleCloseBatchModal();

  // Auto-sincronización instantánea con la nube en segundo plano
  autoSyncPushToCloud();

  showToast(`🎉 Se actualizaron ${updatedCount} puntos (${type}) a: ${STAGES_CONFIG[stage].name}`, 'success');
}

// ==========================================
// EXPORTACIÓN A EXCEL (.xlsx) CON FORMATO INSTITUCIONAL
// ==========================================
window.handleExportExcel = function(onlyFiltered = false) {
  if (typeof XLSX === 'undefined') {
    showToast('La librería de Excel se está cargando...', 'info');
    return;
  }

  const targetList = onlyFiltered ? getReportFilteredPoles() : polesState;

  if (targetList.length === 0) {
    showToast('No hay registros para exportar con los filtros seleccionados', 'error');
    return;
  }

  const PROJECT_NAME = 'MEJORAMIENTO DEL SERVICIO DE SEGURIDAD CIUDADANA EN EL DISTRITO DE ABANCAY, PROVINCIA DE ABANCAY - APURÍMAC';
  const REPORT_TITLE = 'REPORTE DE ESTADO SITUACIONAL DE INSTALACIÓN DE POSTES';
  const LOCATION = 'DISTRITO DE ABANCAY, PROVINCIA DE ABANCAY - DEPARTAMENTO DE APURÍMAC';
  const now = new Date();
  const dateStrFormatted = `${now.toLocaleDateString('es-ES')} ${now.toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit' })}`;

  // Hoja 1: Estado Situacional Detallado
  const padronAoa = [
    [REPORT_TITLE],
    [`PROYECTO: ${PROJECT_NAME}`],
    [`UBICACIÓN: ${LOCATION}  |  SISTEMA DE COORDENADAS: WGS84 UTM ZONA 18 SUR`],
    [`FECHA DE EMISIÓN: ${dateStrFormatted}  |  TOTAL REGISTROS: ${targetList.length}`],
    [], // Fila de separación
    [
      'N°',
      'CÓDIGO',
      'INICIALES',
      'TIPO',
      'COORDENADA ESTE (X)',
      'COORDENADA NORTE (Y)',
      'ETAPA DE OBRA',
      'FECHA'
    ]
  ];

  targetList.forEach((p, idx) => {
    const stageName = (STAGES_CONFIG[p.stage] || STAGES_CONFIG.pendiente).name.toUpperCase();
    const dateDisplay = p.installedAt ? new Date(p.installedAt).toLocaleDateString('es-ES') : '-';
    const typeStr = p.category === '13m' ? '13 Metros (Cámara)' : '9 Metros';

    padronAoa.push([
      idx + 1,
      p.name,
      p.shortName,
      typeStr,
      p.x,
      p.y,
      stageName,
      dateDisplay
    ]);
  });

  const wsPadron = XLSX.utils.aoa_to_sheet(padronAoa);
  wsPadron['!cols'] = [
    { wch: 6 },   // N°
    { wch: 16 },  // CÓDIGO
    { wch: 12 },  // INICIALES
    { wch: 24 },  // TIPO
    { wch: 24 },  // COORDENADA ESTE (X)
    { wch: 24 },  // COORDENADA NORTE (Y)
    { wch: 26 },  // ETAPA DE OBRA
    { wch: 14 }   // FECHA
  ];

  // Hoja 2: Cuadro Resumen por Etapa Constructiva
  const p9m = targetList.filter(p => p.category === '9m');
  const p13m = targetList.filter(p => p.category === '13m');

  const resumenAoa = [
    [REPORT_TITLE],
    [`PROYECTO: ${PROJECT_NAME}`],
    [`CUADRO RESUMEN DE AVANCE POR ETAPAS CONSTRUCTIVAS`],
    [`FECHA: ${dateStrFormatted}  |  TOTAL REGISTROS: ${targetList.length}`],
    [],
    ['ETAPA CONSTRUCTIVA', 'POSTES 9M', 'CÁMARAS 13M', 'TOTAL PUNTOS', '% AVANCE']
  ];

  const stageKeys = [
    { key: 'terminado', label: '🟢 TERMINADOS (Completos)' },
    { key: 'izado_sin_solado', label: '🔵 IZADO SIN SOLADO' },
    { key: 'falta_solado', label: '🟣 FALTA SOLADO' },
    { key: 'excavado', label: '🟡 EXCAVADOS' },
    { key: 'corte', label: '🟧 EN CORTE' },
    { key: 'pendiente', label: '⚪ SIN INICIAR / PENDIENTES' }
  ];

  stageKeys.forEach(st => {
    const c9m = p9m.filter(p => (p.stage || 'pendiente') === st.key).length;
    const c13m = p13m.filter(p => (p.stage || 'pendiente') === st.key).length;
    const totalSt = c9m + c13m;
    const pct = targetList.length > 0 ? ((totalSt / targetList.length) * 100).toFixed(1) + '%' : '0.0%';
    resumenAoa.push([st.label, c9m, c13m, totalSt, pct]);
  });

  resumenAoa.push(['TOTAL GENERAL', p9m.length, p13m.length, targetList.length, '100.0%']);

  const wsResumen = XLSX.utils.aoa_to_sheet(resumenAoa);
  wsResumen['!cols'] = [
    { wch: 34 },
    { wch: 15 },
    { wch: 15 },
    { wch: 15 },
    { wch: 15 }
  ];

  const wb = XLSX.utils.book_new();
  const sheetTitle = onlyFiltered ? `Estado Situacional (${targetList.length})` : 'Estado Situacional General';
  XLSX.utils.book_append_sheet(wb, wsPadron, sheetTitle);
  XLSX.utils.book_append_sheet(wb, wsResumen, 'Resumen de Etapas');

  const filePrefix = onlyFiltered ? 'Reporte_Estado_Situacional_Filtrado_Abancay' : 'Reporte_Estado_Situacional_Postes_Abancay_General';
  XLSX.writeFile(wb, `${filePrefix}_${now.toISOString().slice(0, 10)}.xlsx`);
  showToast(`Excel descargado: ${targetList.length} registros del proyecto Abancay`, 'success');
};

// ==========================================
// EXPORTACIÓN A PDF CON FORMATO INSTITUCIONAL
// ==========================================
window.handleExportPDF = function(onlyFiltered = true) {
  if (typeof window.jspdf === 'undefined' || typeof window.jspdf.jsPDF === 'undefined') {
    showToast('La librería de PDF se está cargando. Intenta nuevamente en unos segundos.', 'info');
    return;
  }

  const targetList = onlyFiltered ? getReportFilteredPoles() : polesState;

  if (targetList.length === 0) {
    showToast('No hay registros para exportar en PDF con los filtros seleccionados', 'error');
    return;
  }

  const { jsPDF } = window.jspdf;
  const doc = new jsPDF({
    orientation: 'landscape',
    unit: 'mm',
    format: 'a4'
  });

  const PROJECT_NAME = 'MEJORAMIENTO DEL SERVICIO DE SEGURIDAD CIUDADANA EN EL DISTRITO DE ABANCAY, PROVINCIA DE ABANCAY - APURÍMAC';
  const REPORT_TITLE = 'REPORTE DE ESTADO SITUACIONAL DE INSTALACIÓN DE POSTES';
  const LOCATION = 'Distrito de Abancay, Provincia de Abancay - Departamento de Apurímac';
  const now = new Date();
  const dateStrFormatted = `${now.toLocaleDateString('es-ES')} ${now.toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit' })}`;

  // 1. Encabezado institucional en primera página
  doc.setFont('helvetica', 'bold');
  doc.setFontSize(13);
  doc.setTextColor(15, 23, 42); // Slate 900
  doc.text(REPORT_TITLE, 14, 12);

  doc.setFontSize(8.5);
  doc.setFont('helvetica', 'bold');
  doc.setTextColor(51, 65, 85); // Slate 700
  doc.text(`PROYECTO: "${PROJECT_NAME}"`, 14, 17, { maxWidth: 268 });

  doc.setFont('helvetica', 'normal');
  doc.setFontSize(7.5);
  doc.setTextColor(100, 116, 139); // Slate 500
  doc.text(`UBICACIÓN: ${LOCATION}   |   SISTEMA: WGS84 UTM ZONA 18S   |   FECHA: ${dateStrFormatted}   |   TOTAL PUNTOS: ${targetList.length}`, 14, 22);

  // Línea divisoria decorativa
  doc.setDrawColor(203, 213, 225);
  doc.setLineWidth(0.4);
  doc.line(14, 24, 283, 24);

  // 2. Cuadro Resumen Ejecutivo por Etapas Constructivas
  const p9m = targetList.filter(p => p.category === '9m');
  const p13m = targetList.filter(p => p.category === '13m');

  const stageKeys = [
    { key: 'terminado', label: 'Terminado' },
    { key: 'izado_sin_solado', label: 'Izado sin Solado' },
    { key: 'falta_solado', label: 'Falta Solado' },
    { key: 'excavado', label: 'Excavado' },
    { key: 'corte', label: 'En Corte' },
    { key: 'pendiente', label: 'Sin Iniciar' }
  ];

  const summaryHead = [['Etapa Constructiva', 'Postes 9m', 'Cámaras 13m', 'Total Puntos', '% Avance']];
  const summaryBody = stageKeys.map(st => {
    const c9m = p9m.filter(p => (p.stage || 'pendiente') === st.key).length;
    const c13m = p13m.filter(p => (p.stage || 'pendiente') === st.key).length;
    const tot = c9m + c13m;
    const pct = targetList.length > 0 ? ((tot / targetList.length) * 100).toFixed(1) + '%' : '0.0%';
    return [st.label, c9m, c13m, tot, pct];
  });
  summaryBody.push(['TOTAL', p9m.length, p13m.length, targetList.length, '100.0%']);

  doc.autoTable({
    startY: 27,
    head: summaryHead,
    body: summaryBody,
    theme: 'grid',
    headStyles: {
      fillColor: [30, 41, 59],
      textColor: [255, 255, 255],
      fontStyle: 'bold',
      fontSize: 7,
      halign: 'center'
    },
    bodyStyles: {
      fontSize: 6.5,
      textColor: [30, 41, 59]
    },
    columnStyles: {
      0: { cellWidth: 38, fontStyle: 'bold' },
      1: { cellWidth: 20, halign: 'center' },
      2: { cellWidth: 20, halign: 'center' },
      3: { cellWidth: 22, halign: 'center', fontStyle: 'bold' },
      4: { cellWidth: 20, halign: 'right', fontStyle: 'bold' }
    },
    margin: { left: 14, right: 14 },
    tableWidth: 120
  });

  const summaryFinalY = doc.lastAutoTable ? doc.lastAutoTable.finalY : 55;

  // 3. Tabla de Detalle Individual de Postes y Cámaras (Sin Lat/Lng ni Google Maps)
  const detailHead = [
    ['N°', 'Código', 'Inicial', 'Tipo', 'Coordenada Este (X)', 'Coordenada Norte (Y)', 'Etapa de Obra', 'Fecha']
  ];

  const detailBody = targetList.map((p, idx) => {
    const stageName = (STAGES_CONFIG[p.stage] || STAGES_CONFIG.pendiente).name;
    const dateStr = p.installedAt ? new Date(p.installedAt).toLocaleDateString('es-ES') : '-';
    const typeStr = p.category === '13m' ? '13m (Cámara)' : '9m (Poste)';

    return [
      idx + 1,
      p.name,
      p.shortName,
      typeStr,
      p.x ? p.x.toFixed(2) : '-',
      p.y ? p.y.toFixed(2) : '-',
      stageName,
      dateStr
    ];
  });

  doc.autoTable({
    startY: summaryFinalY + 6,
    head: detailHead,
    body: detailBody,
    theme: 'striped',
    headStyles: {
      fillColor: [15, 23, 42],
      textColor: [255, 255, 255],
      fontStyle: 'bold',
      fontSize: 7.5,
      halign: 'center'
    },
    bodyStyles: {
      fontSize: 7,
      textColor: [15, 23, 42]
    },
    alternateRowStyles: {
      fillColor: [248, 250, 252]
    },
    columnStyles: {
      0: { cellWidth: 10, halign: 'center', fontStyle: 'bold' },
      1: { cellWidth: 32, fontStyle: 'bold' },
      2: { cellWidth: 18, halign: 'center', fontStyle: 'bold' },
      3: { cellWidth: 32, halign: 'center' },
      4: { cellWidth: 42, halign: 'right', fontStyle: 'bold' },
      5: { cellWidth: 42, halign: 'right', fontStyle: 'bold' },
      6: { cellWidth: 50, halign: 'center', fontStyle: 'bold' },
      7: { cellWidth: 26, halign: 'center' }
    },
    margin: { left: 14, right: 14 },
    didDrawPage: function(data) {
      // Pie de página en todas las páginas del PDF
      const pageCount = doc.internal.getNumberOfPages();
      doc.setFontSize(6.8);
      doc.setTextColor(148, 163, 184);
      doc.text(
        `PosteTrack Pro • Proyecto: Mejoramiento del Servicio de Seguridad Ciudadana en el Distrito de Abancay - Apurímac`,
        14,
        doc.internal.pageSize.height - 6
      );
      doc.text(
        `Página ${data.pageNumber} de ${pageCount}`,
        doc.internal.pageSize.width - 28,
        doc.internal.pageSize.height - 6
      );
    }
  });

  const filePrefix = onlyFiltered ? 'Reporte_Estado_Situacional_Filtrado_Abancay' : 'Reporte_Estado_Situacional_Abancay_General';
  doc.save(`${filePrefix}_${now.toISOString().slice(0, 10)}.pdf`);
  showToast(`📄 PDF descargado: ${targetList.length} registros oficiales`, 'success');
};

// ==========================================
// MODAL: AJUSTES Y CONFIGURACIÓN
// ==========================================
window.handleOpenConfigModal = function() {
  const modal = document.getElementById('modalConfig');
  if (modal) modal.classList.remove('hidden');
};

window.handleCloseConfigModal = function() {
  const modal = document.getElementById('modalConfig');
  if (modal) modal.classList.add('hidden');
};

window.handleExportBackup = function() {
  const dataStr = "data:text/json;charset=utf-8," + encodeURIComponent(localStorage.getItem(STORAGE_KEY) || '{}');
  const dl = document.createElement('a');
  dl.setAttribute("href", dataStr);
  dl.setAttribute("download", `PosteTrack_Backup_GPS_${new Date().toISOString().slice(0, 10)}.json`);
  document.body.appendChild(dl);
  dl.click();
  dl.remove();
  showToast('Respaldo JSON descargado', 'success');
};

window.handleClearAllProgress = function() {
  if (confirm('⚠️ ¿Reiniciar todo a estado "Sin Iniciar"?')) {
    polesState.forEach(p => {
      p.stage = 'pendiente';
      p.crew = '';
      p.installedAt = '';
      p.installNotes = '';
      p.photos = [];
    });
    savePolesToStorage();
    updateDashboard();
    handleCloseConfigModal();
    showToast('Todo reiniciado a estado inicial', 'info');
  }
};

// ==========================================
// FILTROS Y EVENTOS
// ==========================================
window.filterByStage = function(stage) {
  const stageEl = document.getElementById('selectStageFilter');
  if (stageEl) {
    stageEl.value = stage;
    renderPolesTable();
  }
};

window.setTypeFilter = function(type) {
  activeTypeFilter = type;

  const btnAll = document.getElementById('btnFilterTypeAll');
  const btn9m = document.getElementById('btnFilterType9m');
  const btn13m = document.getElementById('btnFilterType13m');
  const txtInd = document.getElementById('txtActiveFilterIndicator');

  const activeAll = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-black rounded-xl bg-slate-900 text-white shadow-sm transition';
  const inactiveAll = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-bold rounded-xl bg-slate-100 hover:bg-slate-200 text-slate-700 transition';

  const active9m = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-black rounded-xl bg-emerald-600 text-white shadow-md transition';
  const inactive9m = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-bold rounded-xl bg-emerald-50 text-emerald-800 border-2 border-emerald-300 hover:bg-emerald-100 transition';

  const active13m = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-black rounded-xl bg-indigo-600 text-white shadow-md transition';
  const inactive13m = 'flex flex-col sm:flex-row items-center justify-center gap-1 py-2 px-1 text-center text-xs font-bold rounded-xl bg-indigo-50 text-indigo-800 border-2 border-indigo-300 hover:bg-indigo-100 transition';

  if (btnAll) btnAll.className = type === 'all' ? activeAll : inactiveAll;
  if (btn9m) btn9m.className = type === '9m' ? active9m : inactive9m;
  if (btn13m) btn13m.className = type === '13m' ? active13m : inactive13m;

  if (txtInd) {
    if (type === 'all') txtInd.textContent = 'Todos (655)';
    else if (type === '9m') txtInd.textContent = '🏗️ Solo 9m (524)';
    else if (type === '13m') txtInd.textContent = '📹 Solo 13m (131)';
  }

  renderPolesTable();
};

window.handleResetFilters = function() {
  const searchEl = document.getElementById('inputSearchPole');
  const stageEl = document.getElementById('selectStageFilter');
  const crewEl = document.getElementById('selectCrewFilter');

  if (searchEl) searchEl.value = '';
  if (stageEl) stageEl.value = 'all';
  if (crewEl) crewEl.value = '';
  setTypeFilter('all');
};

function setupEventListeners() {
  const searchEl = document.getElementById('inputSearchPole');
  const stageEl = document.getElementById('selectStageFilter');
  const crewEl = document.getElementById('selectCrewFilter');
  const formSingle = document.getElementById('formSingleInstall');
  const formBatch = document.getElementById('formBatchInstall');

  if (searchEl) searchEl.addEventListener('input', renderPolesTable);
  if (stageEl) stageEl.addEventListener('change', renderPolesTable);
  if (crewEl) crewEl.addEventListener('change', renderPolesTable);

  if (formSingle) formSingle.addEventListener('submit', (e) => handleSaveSingleInstall(e, false));
  if (formBatch) formBatch.addEventListener('submit', handleSaveBatchInstall);

  const batchFrom = document.getElementById('batchFromNum');
  const batchTo = document.getElementById('batchToNum');
  if (batchFrom) batchFrom.addEventListener('input', updateBatchCountPreview);
  if (batchTo) batchTo.addEventListener('input', updateBatchCountPreview);

  document.querySelectorAll('input[name="batchType"]').forEach(r => r.addEventListener('change', updateBatchCountPreview));

  const cfgZone = document.getElementById('cfgUtmZone');
  if (cfgZone) {
    cfgZone.addEventListener('change', (e) => {
      utmZone = parseInt(e.target.value, 10) || 18;
      polesState.forEach(p => {
        const gps = utmToLatLng(p.x, p.y, utmZone, true);
        p.lat = gps.lat;
        p.lng = gps.lng;
        p.googleMapsUrl = gps.googleMapsUrl;
      });
      updateDashboard();
      showToast(`Zona UTM actualizada a: Zona ${utmZone}S`, 'success');
    });
  }

  const inputImport = document.getElementById('inputImportBackup');
  if (inputImport) {
    inputImport.addEventListener('change', (e) => {
      const file = e.target.files[0];
      if (!file) return;
      const reader = new FileReader();
      reader.onload = (ev) => {
        try {
          const parsed = JSON.parse(ev.target.result);
          localStorage.setItem(STORAGE_KEY, JSON.stringify(parsed));
          initPolesDatabase();
          updateDashboard();
          handleCloseConfigModal();
          showToast('Respaldo restaurado', 'success');
        } catch (err) {
          showToast('Archivo JSON inválido', 'error');
        }
      };
      reader.readAsText(file);
    });
  }

  // Cerrar menú emergente de selección de cuadrillas al hacer clic fuera
  document.addEventListener('click', (e) => {
    const popover = document.getElementById('repCrewMultiCheckboxesContainer');
    const crewSelect = document.getElementById('repFilterCrew');
    const badge = document.getElementById('txtSelectedCrewsCount');
    if (popover && !popover.classList.contains('hidden')) {
      if (!popover.contains(e.target) && !crewSelect?.contains(e.target) && !badge?.contains(e.target)) {
        popover.classList.add('hidden');
      }
    }
  });
}

// ==========================================
// PWA SERVICE WORKER & INSTALADOR MÓVIL
// ==========================================
if ('serviceWorker' in navigator) {
  window.addEventListener('load', () => {
    navigator.serviceWorker.register('./sw.js')
      .then(reg => console.log('Service Worker de PosteTrack Pro activo:', reg.scope))
      .catch(err => console.log('Error registrando Service Worker:', err));
  });
}

let deferredPrompt = null;
window.addEventListener('beforeinstallprompt', (e) => {
  e.preventDefault();
  deferredPrompt = e;
  const btn = document.getElementById('btnInstallAppPrompt');
  if (btn) btn.classList.remove('hidden');
});

window.handleInstallAppClick = function() {
  if (deferredPrompt) {
    deferredPrompt.prompt();
    deferredPrompt.userChoice.then((choiceResult) => {
      if (choiceResult.outcome === 'accepted') {
        showToast('🎉 ¡Instalando PosteTrack Pro en tu celular!', 'success');
      }
      deferredPrompt = null;
    });
  } else {
    // Alerta interactiva directa para celulares
    alert("📲 CÓMO INSTALAR EN TU CELULAR:\n\n1. En Google Chrome, toca los 3 puntos (⋮) arriba a la derecha.\n2. Toca en 'Agregar a la pantalla principal' o 'Instalar aplicación'.\n3. ¡Listo! Tendrás el icono de PosteTrack Pro en la pantalla de tu celular.");
    handleOpenSyncModal();
    switchSyncTab('qr');
  }
};

// ==========================================
// MODAL: SINCRONIZACIÓN CELULAR ↔ PC
// ==========================================
window.handleOpenSyncModal = function() {
  const modal = document.getElementById('modalSyncData');
  if (modal) {
    modal.classList.remove('hidden');
    updateSyncQrDisplay();
    if (window.lucide && typeof window.lucide.createIcons === 'function') {
      window.lucide.createIcons();
    }
  }
};

window.handleCloseSyncModal = function() {
  const modal = document.getElementById('modalSyncData');
  if (modal) modal.classList.add('hidden');
};

window.switchSyncTab = function(tabName) {
  const tabs = ['cloud', 'qr', 'file'];
  tabs.forEach(t => {
    const btn = document.getElementById(`tabBtn${capitalize(t)}Sync`) || document.getElementById(`tabBtn${capitalize(t)}Backup`);
    const content = document.getElementById(`tabContent${capitalize(t)}`);
    if (btn) {
      if (t === tabName) {
        btn.className = 'flex-1 py-2.5 px-3 text-center border-b-2 border-indigo-600 text-indigo-600 bg-white flex items-center justify-center gap-1.5 transition font-black';
      } else {
        btn.className = 'flex-1 py-2.5 px-3 text-center border-b-2 border-transparent text-slate-500 hover:text-slate-800 flex items-center justify-center gap-1.5 transition font-bold';
      }
    }
    if (content) {
      if (t === tabName) content.classList.remove('hidden');
      else content.classList.add('hidden');
    }
  });

  if (tabName === 'qr') updateSyncQrDisplay();
  if (window.lucide) window.lucide.createIcons();
};

function capitalize(s) {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

function updateSyncQrDisplay() {
  const currentHost = window.location.host;
  let targetUrl = window.location.href;
  if (!currentHost || currentHost === '' || window.location.protocol === 'file:') {
    targetUrl = 'http://192.168.1.50:8080/';
  }
  const inputUrl = document.getElementById('inputLocalServerUrl');
  if (inputUrl) inputUrl.value = targetUrl;

  const imgQr = document.getElementById('imgQrCodeDisplay');
  if (imgQr) {
    imgQr.src = `https://api.qrserver.com/v1/create-qr-code/?size=200x200&data=${encodeURIComponent(targetUrl)}`;
  }
}

// ------------------------------------------
// MOTOR DE SINCRONIZACIÓN EN TIEMPO REAL (CLOUD AUTO-SYNC)
// ------------------------------------------
const CLOUD_STORAGE_KEY_PREFIX = 'postetrack_cloud_sync_';
let autoSyncIntervalId = null;
let lastCloudSyncTimestamp = '';
let isSyncingInProgress = false;

// BroadcastChannel para sincronización instantánea entre pestañas en la misma máquina
let localBroadcastChannel = null;
try {
  localBroadcastChannel = new BroadcastChannel('postetrack_realtime_sync');
  localBroadcastChannel.onmessage = (event) => {
    if (event.data && event.data.type === 'POLES_UPDATED') {
      handlePullDataFromCloud(true);
    }
  };
} catch (e) {}

function getActiveProjectCode() {
  const codeInput = document.getElementById('inputSyncProjectCode');
  if (codeInput && codeInput.value.trim()) {
    return codeInput.value.trim();
  }
  return localStorage.getItem('postetrack_active_project_code') || 'ABANCAY-SEGURIDAD-2026';
}

const NTFY_SYNC_TOPIC = 'postetrack_abancay_2026_sync';
const NTFY_SYNC_URL = `https://ntfy.sh/${NTFY_SYNC_TOPIC}`;
let ntfyEventSource = null;

function connectRealtimeSyncStream() {
  if (ntfyEventSource) {
    try { ntfyEventSource.close(); } catch (e) {}
  }

  try {
    if (window.EventSource) {
      ntfyEventSource = new EventSource(`${NTFY_SYNC_URL}/sse`);
      
      ntfyEventSource.onmessage = function(event) {
        try {
          const data = JSON.parse(event.data);
          if (data.message) {
            const remotePayload = JSON.parse(data.message);
            applyRemoteSyncPayload(remotePayload, true);
          }
        } catch (e) {}
      };

      ntfyEventSource.onerror = function() {
        try { ntfyEventSource.close(); } catch (e) {}
        ntfyEventSource = null;
        setTimeout(connectRealtimeSyncStream, 5000);
      };
    }
  } catch (err) {
    console.warn('[EventSource Error]:', err);
  }
}

function startLiveAutoSync() {
  if (autoSyncIntervalId) clearInterval(autoSyncIntervalId);

  // 1. Conectar flujo en tiempo real (Sub-segundo instantáneo)
  connectRealtimeSyncStream();

  // 2. Recuperar últimos avances de la nube al abrir la app
  setTimeout(() => {
    handlePullDataFromCloud(true);
  }, 300);

  // 3. Sondeo de respaldo cada 5 segundos
  autoSyncIntervalId = setInterval(() => {
    handlePullDataFromCloud(true);
  }, 5000);

  updateLiveSyncBannerUI('ready');
}

function autoSyncPushToCloud() {
  handlePushDataToCloud(true);
  if (localBroadcastChannel) {
    try {
      localBroadcastChannel.postMessage({ type: 'POLES_UPDATED', timestamp: Date.now() });
    } catch (e) {}
  }
}

window.handleTriggerManualSync = async function() {
  const spinner = document.getElementById('iconSyncSpinner');
  if (spinner) spinner.classList.add('animate-spin');

  await handlePushDataToCloud(false);
  await handlePullDataFromCloud(false);

  if (spinner) {
    setTimeout(() => spinner.classList.remove('animate-spin'), 600);
  }
};

window.handlePushDataToCloud = async function(silent = false) {
  const projectCode = getActiveProjectCode();
  const btn = document.getElementById('btnPushToCloud');

  if (!silent && btn) {
    btn.disabled = true;
    btn.innerHTML = '<i data-lucide="loader-2" class="w-4 h-4 animate-spin"></i> Subiendo a la nube...';
  }

  updateLiveSyncBannerUI('uploading');

  try {
    const changedPoles = polesState
      .filter(p => (p.stage && p.stage !== 'pendiente') || p.crew || p.installedAt || p.installNotes || (p.photos && p.photos.length > 0))
      .map(p => ({
        id: p.id,
        stage: p.stage || 'pendiente',
        crew: p.crew || '',
        installedAt: p.installedAt || '',
        installNotes: p.installNotes || '',
        photos: p.photos || []
      }));

    const payload = {
      projectCode: projectCode,
      updatedAt: new Date().toISOString(),
      senderDevice: (window.innerWidth >= 768 ? 'Laptop' : 'Celular') + '_' + Math.random().toString(36).substr(2, 4),
      totalProgressCount: changedPoles.length,
      poles: changedPoles
    };

    lastCloudSyncTimestamp = payload.updatedAt;

    const payloadStr = JSON.stringify(payload);

    await fetch(NTFY_SYNC_URL, {
      method: 'POST',
      body: payloadStr,
      headers: {
        'Title': 'PosteTrack Sync',
        'Tags': 'package'
      }
    });

    const timeStr = new Date().toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit', second: '2-digit' });
    const txtLast = document.getElementById('txtLastSyncTime');
    if (txtLast) txtLast.textContent = `Subido hoy a las ${timeStr}`;

    updateLiveSyncBannerUI('synced', timeStr);

    if (!silent) {
      showToast(`☁️ ¡Datos subidos a la nube en tiempo real! (${timeStr})`, 'success');
    }
  } catch (err) {
    console.error('[Cloud Auto-Push Error]:', err);
    if (!silent) showToast('Error de conexión al sincronizar con la nube', 'error');
  } finally {
    if (!silent && btn) {
      btn.disabled = false;
      btn.innerHTML = '<i data-lucide="cloud-upload" class="w-4 h-4"></i> <span>☁️ Subir Avances a la Central</span>';
      if (window.lucide) window.lucide.createIcons();
    }
  }
};

function applyRemoteSyncPayload(remoteData, fromStream = false) {
  if (!remoteData || !Array.isArray(remoteData.poles)) return;

  if (remoteData.updatedAt && remoteData.updatedAt === lastCloudSyncTimestamp) {
    return;
  }

  lastCloudSyncTimestamp = remoteData.updatedAt || new Date().toISOString();

  let updatedCount = 0;
  const remotePolesMap = new Map();
  remoteData.poles.forEach(rp => remotePolesMap.set(rp.id, rp));

  polesState.forEach(localPole => {
    const remote = remotePolesMap.get(localPole.id);
    if (remote) {
      let changed = false;
      if (remote.stage !== localPole.stage) {
        localPole.stage = remote.stage;
        changed = true;
      }
      if (remote.crew !== localPole.crew) {
        localPole.crew = remote.crew || '';
        changed = true;
      }
      if (remote.installedAt !== localPole.installedAt) {
        localPole.installedAt = remote.installedAt || '';
        changed = true;
      }
      if (remote.installNotes !== localPole.installNotes) {
        localPole.installNotes = remote.installNotes || '';
        changed = true;
      }
      if (JSON.stringify(remote.photos || []) !== JSON.stringify(localPole.photos || [])) {
        localPole.photos = remote.photos || [];
        changed = true;
      }

      if (changed) updatedCount++;
    } else {
      if (localPole.stage !== 'pendiente' || localPole.crew || (localPole.photos && localPole.photos.length > 0)) {
        localPole.stage = 'pendiente';
        localPole.crew = '';
        localPole.installedAt = '';
        localPole.installNotes = '';
        localPole.photos = [];
        updatedCount++;
      }
    }
  });

  savePolesToStorage();
  populateCrewFilters();
  updateDashboard();
  renderPolesTable();

  const repModal = document.getElementById('modalReports');
  if (repModal && !repModal.classList.contains('hidden')) {
    renderReportsView();
  }

  const timeStr = new Date().toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  const txtLast = document.getElementById('txtLastSyncTime');
  if (txtLast) txtLast.textContent = `Sincronizado hoy a las ${timeStr}`;

  updateLiveSyncBannerUI('synced', timeStr);

  if (updatedCount > 0) {
    showToast(`⚡ Sincronización en vivo: ${updatedCount} poste(s) actualizados (${timeStr})`, 'info');
  }
}

window.handlePullDataFromCloud = async function(silent = false) {
  if (isSyncingInProgress) return;
  isSyncingInProgress = true;

  const btn = document.getElementById('btnPullFromCloud');

  if (!silent && btn) {
    btn.disabled = true;
    btn.innerHTML = '<i data-lucide="loader-2" class="w-4 h-4 animate-spin"></i> Sincronizando...';
  }

  try {
    const resp = await fetch(`${NTFY_SYNC_URL}/json?since=24h&poll=1`);
    if (!resp.ok) return;

    const rawText = await resp.text();
    const lines = rawText.split('\n').filter(l => l.trim());

    let latestPayload = null;
    for (const line of lines) {
      try {
        const obj = JSON.parse(line);
        if (obj.message) {
          const msgPayload = JSON.parse(obj.message);
          if (msgPayload && msgPayload.poles) {
            latestPayload = msgPayload;
          }
        }
      } catch (e) {}
    }

    if (latestPayload) {
      applyRemoteSyncPayload(latestPayload, false);
      if (!silent) {
        if (typeof confetti === 'function') confetti({ particleCount: 30, spread: 50, origin: { y: 0.6 } });
        showToast(`🎉 ¡Sincronizado con éxito con la nube!`, 'success');
      }
    }
  } catch (err) {
    console.error('[Cloud Pull Error]:', err);
    if (!silent) showToast('Error al descargar datos de la nube', 'error');
  } finally {
    isSyncingInProgress = false;
    if (!silent && btn) {
      btn.disabled = false;
      btn.innerHTML = '<i data-lucide="cloud-download" class="w-4 h-4"></i> <span>⬇️ Actualizar Datos en mi PC</span>';
      if (window.lucide) window.lucide.createIcons();
    }
  }
};

function updateLiveSyncBannerUI(status, timeStr = '') {
  const ping = document.getElementById('pingLiveSync');
  const dot = document.getElementById('dotLiveSync');
  const txtLastPing = document.getElementById('txtLiveSyncLastPing');
  const txtChannel = document.getElementById('txtDisplaySyncChannel');

  if (txtChannel) {
    txtChannel.textContent = getActiveProjectCode();
  }

  if (txtLastPing && timeStr) {
    txtLastPing.textContent = `Última sincronización: ${timeStr}`;
  }

  if (status === 'uploading') {
    if (dot) dot.className = 'relative inline-flex rounded-full h-2.5 w-2.5 bg-amber-500';
    if (ping) ping.className = 'animate-ping absolute inline-flex h-full w-full rounded-full bg-amber-400 opacity-75';
  } else {
    if (dot) dot.className = 'relative inline-flex rounded-full h-2.5 w-2.5 bg-emerald-500';
    if (ping) ping.className = 'animate-ping absolute inline-flex h-full w-full rounded-full bg-emerald-400 opacity-75';
  }
}

// ------------------------------------------
// EXPORTACIÓN E IMPORTACIÓN RÁPIDA (WHATSAPP / ARCHIVO)
// ------------------------------------------
window.handleExportSyncPackage = function() {
  const payload = {
    project: 'MEJORAMIENTO DEL SERVICIO DE SEGURIDAD CIUDADANA EN EL DISTRITO DE ABANCAY',
    exportedAt: new Date().toISOString(),
    poles: polesState
  };

  const dataStr = "data:text/json;charset=utf-8," + encodeURIComponent(JSON.stringify(payload));
  const dl = document.createElement('a');
  dl.setAttribute("href", dataStr);
  dl.setAttribute("download", `Avance_Postes_Abancay_${new Date().toISOString().slice(0, 10)}.json`);
  document.body.appendChild(dl);
  dl.click();
  dl.remove();
  showToast('📁 Archivo de avance generado para compartir por WhatsApp', 'success');
};

window.handleImportSyncPackage = function(event) {
  const file = event.target.files[0];
  if (!file) return;

  const reader = new FileReader();
  reader.onload = (e) => {
    try {
      const parsed = JSON.parse(e.target.result);
      const incomingPoles = parsed.poles || (Array.isArray(parsed) ? parsed : null);

      if (!incomingPoles) {
        showToast('El archivo no contiene datos válidos de postes', 'error');
        return;
      }

      let updatedCount = 0;
      const incomingMap = new Map();
      incomingPoles.forEach(p => incomingMap.set(p.id, p));

      polesState.forEach(p => {
        const inc = incomingMap.get(p.id);
        if (inc) {
          if (inc.stage && inc.stage !== 'pendiente') p.stage = inc.stage;
          if (inc.crew) p.crew = inc.crew;
          if (inc.installedAt) p.installedAt = inc.installedAt;
          if (inc.installNotes) p.installNotes = inc.installNotes;
          if (inc.photos && inc.photos.length > 0) p.photos = inc.photos;
          updatedCount++;
        }
      });

      savePolesToStorage();
      populateCrewFilters();
      updateDashboard();
      renderPolesTable();
      handleCloseSyncModal();

      showToast(`🎉 ¡Sincronizado! Se integraron los datos del archivo en tu PC`, 'success');
    } catch (err) {
      showToast('Error al leer el archivo de sincronización', 'error');
    }
  };
  reader.readAsText(file);
};

function showToast(msg, type = 'info') {
  const container = document.getElementById('toastContainer');
  if (!container) return;

  const toast = document.createElement('div');
  const colors = {
    success: 'bg-emerald-800 text-white border-emerald-600',
    error: 'bg-red-800 text-white border-red-600',
    info: 'bg-slate-800 text-white border-slate-700'
  };

  toast.className = `toast flex items-center gap-2 px-3.5 py-2 rounded-xl shadow-xl text-xs font-bold border ${colors[type] || colors.info}`;
  toast.textContent = msg;

  container.appendChild(toast);
  setTimeout(() => toast.classList.add('show'), 10);
  setTimeout(() => {
    toast.classList.remove('show');
    setTimeout(() => toast.remove(), 300);
  }, 3500);
}

function escapeHtml(str) {
  if (!str) return '';
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}
