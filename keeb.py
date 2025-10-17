#!/usr/bin/env python3

import urllib.request
import urllib.error
import socket
import shutil
import zipfile
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
import re
import math
import random
import multiprocessing
import copy
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import traceback
from ast import literal_eval
import signal
from dataclasses import dataclass, field, fields
import statistics
import sys

@dataclass
class Score:
	effort: int = 0
	sfb: int = 0
	rollin: int = 0
	scissors: int = 0

@dataclass
class Layout:
	letters: list[list[str]]
	score: Score = field(default_factory=lambda: Score())
	total: int = 0
	left_usage: int = 0
	right_usage: int = 0

	def clone(self):
		return Layout([row[:] for row in self.letters])

	def __post_init__(self):
		self.letters = copy.deepcopy(self.letters)
		self.calc_scores()
		if SCORE_MEDIAN is not None:
			self.calc_total_score()

	def __eq__(self, other):
		if not isinstance(other, Layout):
			return False
		return self.letters == other.letters

	def __hash__(self):
		return hash(tuple(tuple(r) for r in self.letters))

	def calc_scores(self):
		self.score = Score()
		self.left_usage = 0
		self.right_usage = 0
		pos = {}

		for r in range(3):
			for c in range(10):
				ch = self.letters[r][c]
				if ch != ' ':
					pos[ch] = (r, c)
					try:
						l = LETTERS[ch]
					except KeyError:
						print('======= ERROR')
						print_layout(self)
						sys.exit(1)
					self.score.effort += l * EFFORT_GRID[r][c]
					if c < 5:
						self.left_usage += l
					else:
						self.right_usage += l

		for pair, count in BIGRAMS.items():
			a, b = pair[0], pair[1]
			if a not in pos or b not in pos:
				continue
			r1, c1 = pos[a]
			r2, c2 = pos[b]
			f1 = FINGER_GRID[r1][c1]
			f2 = FINGER_GRID[r2][c2]
			if f1 == f2:
				self.score.sfb += count
			elif (f1 - f2) == 1:
				if f2 < f1 and abs(r1 - r2) <= 1:
					self.score.rollin += count
				elif abs(r1 - r2) == 2:
					self.score.scissors += count

	def calc_total_score(self):
		def norm(v, m, d):
			return (v - m) / d if d != 0 else 0.0

		r = Score(
			effort=norm(self.score.effort, SCORE_MEDIAN.effort, SCORE_IQR.effort),
			sfb=norm(self.score.sfb, SCORE_MEDIAN.sfb, SCORE_IQR.sfb),
			rollin=norm(self.score.rollin, SCORE_MEDIAN.rollin, SCORE_IQR.rollin),
			scissors=norm(self.score.scissors, SCORE_MEDIAN.scissors, SCORE_IQR.scissors),
		)

		self.total = (
			(-r.effort) * SCORE_RATES.effort +
			(-r.sfb) * SCORE_RATES.sfb +
			(r.rollin) * SCORE_RATES.rollin +
			(-r.scissors) * SCORE_RATES.scissors
		)

TMP_PATH = None
ANALYZE_RESULT_FILENAME = 'analyze_result.tsv'
BEST_RESULT_FILENAME = 'best.txt'

LETTERS = Counter()
BIGRAMS = Counter()

EFFORT_GRID = [
	[20, 2, 2, 2, 9, 10, 3, 3, 3, 20],
	[ 1, 0, 0, 0, 5, 6,  1, 1, 1,  2],
	[20, 2, 2, 1, 7, 8,  2, 3, 3, 20],
]

FINGER_GRID = [
	[4, 3, 2, 1, 1, 1, 1, 2, 3, 4],
	[4, 3, 2, 1, 1, 1, 1, 2, 3, 4],
	[4, 3, 2, 1, 1, 1, 1, 2, 3, 4],
]

SCORE_RATES = Score(
	effort = 0.3,
	sfb = 0.2,
	rollin = 0.1,
	scissors = 0.4,
)
SCORE_MEDIAN = None
SCORE_IQR = None

def layout_key(l):
	return (
		l.total,
		l.left_usage,
		-l.score.scissors,
		-l.score.effort,
		-l.score.sfb,
		l.score.rollin
	)

def best_layout(layouts: list[Layout]):
	return max(layouts, key=layout_key).clone()

def sort_layouts(layouts: list[Layout]):
	layouts.sort(key=layout_key, reverse=True)
	return layouts

def init_score_state():
	global SCORE_MEDIAN, SCORE_IQR 
	def iqr(v):
		q = statistics.quantiles(v, n=4)
		return q[2] - q[0]

	base_layout = make_initial_layout()
	unique_layouts = {base_layout.clone()}
	while len(unique_layouts) < 100:
		unique_layouts.add(make_random(base_layout))
	layouts = list(unique_layouts)

	vals = {f.name: [getattr(l.score, f.name) for l in layouts] for f in fields(Score)}

	SCORE_MEDIAN = Score(**{k: statistics.median(v) for k, v in vals.items()})

	iqr_map = {}
	for k, v in vals.items():
		d = iqr(v)
		iqr_map[k] = d if d != 0 else 1e-9
	SCORE_IQR = Score(**iqr_map)

def check_target_url(url):
	try:
		req = urllib.request.Request(url, method='HEAD')
		with urllib.request.urlopen(req, timeout=5) as res:
			if res.status == 200: return True
	except (urllib.error.HTTPError, urllib.error.URLError, socket.timeout): pass

	return False

def download_target(url, dest):
	repo_name = url.rstrip('/').split('/')[-1]
	base_url = url.rstrip('/') + '/archive/refs/heads/'

	for u in [base_url+'master.zip', base_url+'main.zip']:
		try:
			with urllib.request.urlopen(u) as res:
				z = os.path.join(dest, f'{repo_name}.zip')
				with open(z, 'wb') as f:
					while True:
						buf = res.read(8192)
						if not buf:
							break
						f.write(buf)

			with zipfile.ZipFile(z, 'r') as zz:
				zz.extractall(dest)
			os.remove(z)
			return True
		except (urllib.error.HTTPError, urllib.error.URLError, socket.timeout):
			try: os.remove(z)
			except: pass

	return False

def cleanup(sig, frame):
	global TMP_PATH
	try:
		if TMP_PATH and os.path.exists(TMP_PATH):
			shutil.rmtree(TMP_PATH)
	except Exception:
		pass
	sys.exit(1)

def save_analyze_result(result_path):
	file_path = os.path.join(result_path, ANALYZE_RESULT_FILENAME)

	with open(file_path, 'w', encoding='utf-8') as f:
		f.write('letter\tfrequency\n')
		for ch, count in LETTERS.most_common():
			f.write(f'{ch}\t{count}\n')

		f.write('\nbigram\tfrequency\n')
		for bg, count in BIGRAMS.most_common():
			f.write(f'{bg}\t{count}\n')

def load_analysis_result(result_path):
	global LETTERS, BIGRAMS

	file_path = os.path.join(result_path, ANALYZE_RESULT_FILENAME)

	with open(file_path, 'r', encoding='utf-8') as f:
		section = None
		for line in f:
			line = line.strip()
			if not line:
				continue
			if line.startswith('letter\t'):
				section = 'letters'
				continue
			elif line.startswith('bigram\t'):
				section = 'bigrams'
				continue

			if section == 'letters':
				ch, count = line.split('\t')
				LETTERS[ch] = int(count)
			elif section == 'bigrams':
				bg, count = line.split('\t')
				BIGRAMS[bg] = int(count)

def analyze_target_single(full_path):
	letters = Counter()
	bigrams = Counter()
	pattern = re.compile('[a-z]+', re.IGNORECASE)
	try:
		with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
			groups = pattern.findall(f.read())
			for g in groups:
				word = g.lower()
				word = [ch for ch in word if 'a' <= ch <= 'z']
				for ch in word:
					letters[ch] += 1
				for i in range(len(word)-1):
					if word[i] != word[i+1]:
						bigrams[word[i] + word[i+1]] += 1
	except (FileNotFoundError, PermissionError, IsADirectoryError) as e:
		print(f'Failed: {full_path} — {e}')
	return letters, bigrams

def analyze_target(result_path):
	global LETTERS, BIGRAMS, TMP_PATH

	targets = [
		'https://github.com/torvalds/linux',
		'https://github.com/opencv/opencv',
		'https://github.com/django/django',
		'https://github.com/facebook/react',
		'https://github.com/microsoft/vscode',
		'https://github.com/kubernetes/kubernetes',
		'https://github.com/ohmyzsh/ohmyzsh',
		'https://github.com/rails/rails',
		'https://github.com/git/git',
		'https://github.com/openssl/openssl',
		'https://github.com/mirror/busybox',
		'https://github.com/gcc-mirror/gcc',
		'https://github.com/curl/curl',
		'https://github.com/nginx/nginx',
		'https://github.com/tmux/tmux',
		'https://github.com/bminor/glibc',
		'https://github.com/sqlite/sqlite',
		'https://github.com/python/cpython',
		'https://github.com/numpy/numpy',
		'https://github.com/psf/requests',
	]
	extensions = {
		'.c', '.h',
		'.cpp', '.hpp',
		'.cc', '.hh',
		'.s', '.S',
		'.cs',
		'.java',
		'.py',
		'.js', '.ts',
		'.go',
		'.rs',
		'.php',
		'.swift',
		'.kt', '.kts',
		'.rb',
		'.m', '.mm',
		'.sh', '.bash', '.zsh',
		'.pl', '.pm',
		'.lua',
		'.md'
	}

	# Check
	print('[Check Target]')
	len_targets = len(targets)
	for i, url in enumerate(targets, 1):
		if check_target_url(url):
			print(f'\r\033[K{i}/{len_targets} ({i/len_targets*100:.1f}%) {url}', end='')

		else:
			print(f'\n[FAIL] {url}')
	print(f'\r\033[K...Done')

	# Download
	TMP_PATH = tempfile.mkdtemp(dir=os.path.expanduser('~'), prefix='keeb')
	print('[Download Target]')
	downloaded = 0
	with ThreadPoolExecutor(max_workers=8) as executor:
		futures = [executor.submit(download_target, url, TMP_PATH) for url in targets]
		for future in as_completed(futures):
			future.result()
			downloaded += 1
			print(f'\r\033[K{downloaded}/{len_targets} ({downloaded/len_targets*100:.1f}%)', end='')
	print(f'\r\033[K...Done')

	# file list
	files = []
	for root, dirs, fs in os.walk(TMP_PATH):
		for file in fs:
			_, ext = os.path.splitext(file)
			if ext in extensions:
				files.append(os.path.join(root, file))

	# Calc LETTERS, BIGRAMS
	print('[Analyze Target]')
	letters = Counter()
	bigrams = Counter()
	len_files = len(files)
	with ProcessPoolExecutor() as executor:
		for i, (l, b) in enumerate(executor.map(analyze_target_single, files), 1):
			letters += l
			bigrams += b
			print(f'\r\033[K{i}/{len_files} ({i/len_files*100:.1f}%)', end='')

	LETTERS = letters
	total_count = sum(bigrams.values())
	threshold = total_count * 0.9
	cumulative = 0
	for bigram, count in bigrams.most_common():
		cumulative += count
		BIGRAMS[bigram] = count
		if cumulative >= threshold:
			break

	shutil.rmtree(TMP_PATH)
	print(f'\r\033[K...Done')

	# Store result
	save_analyze_result(result_path)

def make_initial_layout() -> Layout:
	grid = [] 
	coords = []
	for r in range(3):
		for c in range(10):
			coords.append((EFFORT_GRID[r][c], r, c))
	coords.sort()

	letters_sorted = [ch for ch, _ in LETTERS.most_common()]
	layout = [[' ' for _ in range(10)] for _ in range(3)]
	for i, (_, r, c) in enumerate(coords):
		if i < len(letters_sorted):
			layout[r][c] = letters_sorted[i]

	return Layout(layout)

def make_random(base_layout: Layout) -> Layout:
	layout = base_layout.clone()

	positions = [(i, j) for i in range(len(layout.letters)) for j in range(len(layout.letters[0])) if layout.letters[i][j] != ' ']
	keys = [layout.letters[i][j] for i, j in positions]
	random.shuffle(keys)

	for idx, (i, j) in enumerate(positions):
		layout.letters[i][j] = keys[idx]

	return layout

def crossover(parents: list[Layout], blank=' '):
	def flatten(layout):
		return [item for row in layout for item in row]
	def unflatten(flat, rows=3, cols=10):
		return [flat[i*cols:(i+1)*cols] for i in range(rows)]

	parent1 = flatten(parents[0].letters)
	parent2 = flatten(parents[1].letters)
	length = len(parent1)

	a, b = sorted(random.sample(range(length), 2))
	child = [blank if k == blank else None for k in parent1]
	child[a:b] = parent1[a:b]

	used = {k for k in child if k is not None}
	remain_keys = [k for k in parent2 if k not in used]
	it = iter(remain_keys)
	for i in range(length):
		if child[i] is None:
			child[i] = next(it)

	return Layout(unflatten(child))

def fine_tune_effort(base_layout: Layout):
	letters = [row[:] for row in base_layout.letters]
	positions = [(r,c) for r in range(3) for c in range(10) if letters[r][c] != ' ']
	positions.sort(key=lambda pos: LETTERS.get(letters[pos[0]][pos[1]],0), reverse=True)
	candidates = [base_layout.clone()]

	for (r,c) in positions:
		l = [row[:] for row in base_layout.letters]
		best = (r,c)
		for dr in (-1,0,1):
			for dc in (-1,0,1):
				nr,nc=r+dr,c+dc
				if 0<=nr<3 and 0<=nc<10 and l[nr][nc]!=' ':
					if EFFORT_GRID[nr][nc] < EFFORT_GRID[best[0]][best[1]]:
						best = (nr,nc)
		l[r][c], l[best[0]][best[1]] = l[best[0]][best[1]], l[r][c]
		candidates.append(Layout(l))

	return best_layout(candidates)

def optimize_effort(base_layout: Layout):
	orders = ['effort_asc', 'effort_desc', 'count_asc', 'count_desc']
	letters = [row[:] for row in base_layout.letters]
	layouts = {base_layout.clone()}

	for order in orders:
		effort_levels = list({val for row in EFFORT_GRID for val in row if val < 10})

		if order == 'effort_asc':
			effort_levels.sort()
		elif order == 'effort_desc':
			effort_levels.sort(reverse=True)
		else:
			effort_counts = {val: sum(1 for r in range(3) for c in range(10) if EFFORT_GRID[r][c] == val) for val in effort_levels}
			if order == 'count_asc':
				effort_levels.sort(key=lambda x: effort_counts[x])
			elif order == 'count_desc':
				effort_levels.sort(key=lambda x: -effort_counts[x])

		for effort_level in effort_levels:
			group_coords = [(r, c) for r in range(3) for c in range(10) if abs(EFFORT_GRID[r][c] - effort_level) <= 1]
			random.shuffle(group_coords)

			for i in range(len(group_coords)):
				r1, c1 = group_coords[i]
				for j in range(i+1, len(group_coords)):
					r2, c2 = group_coords[j]
					if letters[r1][c1] == ' ' and letters[r2][c2] == ' ':
						continue
					l = [row[:] for row in letters]
					l[r1][c1], l[r2][c2] = l[r2][c2], l[r1][c1]
					layouts.add(Layout(l))
	
	return best_layout(list(layouts))

def optimize_swap(base_layout: Layout, temperature, fix=0):
	n = None
	if fix == 0:
		if temperature > 50:
			n = random.choices([4, 5, 6], weights=[0.5, 0.3, 0.2], k=1)[0]
		elif temperature > 10:
			n = random.choices([3, 4], weights=[0.7, 0.3], k=1)[0]
		else:
			n = random.choices([2, 3], weights=[0.8, 0.2], k=1)[0]
	else:
		n = fix

	coords = set()
	while len(coords) < n:
		r, c = random.randint(0, 2), random.randint(0, 9)
		if base_layout.letters[r][c] != ' ':
			coords.add((r, c))
	coords = list(coords)

	letters = [row[:] for row in base_layout.letters]

	shuffled = coords[:]
	random.shuffle(shuffled)

	for i in range(n):
		r1, c1 = coords[i]
		r2, c2 = shuffled[i]
		letters[r1][c1], letters[r2][c2] = letters[r2][c2], letters[r1][c1]

	return Layout(letters)

def optimize_all_swap(base_layout: Layout):
	letters = [row[:] for row in base_layout.letters]
	positions = [(r, c) for r in range(3) for c in range(10) if letters[r][c] != ' ']

	layouts = [base_layout.clone()]

	for i in range(len(positions)):
		r1, c1 = positions[i]
		for j in range(i + 1, len(positions)):
			r2, c2 = positions[j]
			l = [row[:] for row in letters]
			l[r1][c1], l[r2][c2] = l[r2][c2], l[r1][c1]
			layouts.append(Layout(l))

	return best_layout(layouts)

def optimize_sa(base_layout: Layout, max_iter=10000, initial_temp=50.0, cooling_rate=0.9985, max_unimproved=2000):
	best = base_layout.clone()
	cur = base_layout.clone()
	temperature = initial_temp
	unimproved = 0

	for i in range(max_iter):
		new_layout = optimize_swap(cur, temperature)

		diff = new_layout.total - cur.total
		T = max(temperature, 1e-6)
		try:
			prob = math.exp(diff / T)
		except (OverflowError, ZeroDivisionError, TypeError):
			prob = 1.0

		unimproved += 1
		if diff >= 0 or prob > random.random():
			cur = new_layout
			if cur.total > best.total:
				best = cur.clone()
				temperature *= 1.05
				unimproved = 0
		temperature *= cooling_rate

		if unimproved > max_unimproved or temperature < 1e-3:
			break

	return best

def optimize(base_layout: Layout, max_generation=10, max_population=100):
	best = base_layout.clone()

	# Init population
	unique_population = {best.clone()}
	while len(unique_population) < max_population:
		unique_population.add(make_random(best))
	population = sort_layouts(list(unique_population))
	
	elites_len = max(1, int(max_population * 0.05))
	with ProcessPoolExecutor() as executor:
		for gen in range(1, max_generation+1):
			print(f'\r\033[K...{gen}/{max_generation}', end='')
			random_len = int(max_population* max(0.05, 0.3 * (1 - gen/ max_generation)))

			elites = [l.clone() for l in population[:elites_len]]
			parents = [best_layout(random.sample(population, 3)) for _ in range(max_population)]
			children = [crossover(random.sample(parents, 2)) for _ in range(max_population - elites_len - random_len)]

			# Make next
			population = []
			for elite in elites:
				population.append(fine_tune_effort(elite))
			for _ in range(random_len):
				population.append(make_random(best))
			progress = min(gen/max_generation, 1.0)
			results = list(executor.map(
				optimize_worker,
				children,
				[progress] * len(children)
			))
			population.extend(results)

			cur = best_layout(population)
			if cur.total > best.total:
				best = cur

	return best

def optimize_worker(layout: Layout, progress):
	sa_weight = 0.2 + 0.2 * progress   # 0.2 - 0.4
	effort_weight = 0.2 + 0.1 * progress  # 0.2 - 0.3
	swap_weight = 0.3 - 0.05 * progress  # 0.3 - 0.25
	pass_weight = 1.0 - (sa_weight + effort_weight + swap_weight)

	weights = [max(0.0, sa_weight), max(0.0, effort_weight), max(0.0, swap_weight), max(0.0, pass_weight)]
	total = sum(weights)
	if total <= 0:
		weights = [0.25] * 4
		total = 1.0
	thresholds = []
	acc = 0.0
	for w in weights:
		acc += w / total
		thresholds.append(acc)

	r = random.random()
	if r < thresholds[0]:
		return optimize_sa(layout)
	elif r < thresholds[1]:
		return optimize_effort(layout)
	elif r < thresholds[2]:
		return optimize_all_swap(layout)
	else:
		return layout

def print_layout(layout: Layout):
	print(f'{layout.score.effort:,}\t', end='')
	print(f'{layout.score.sfb:,}\t', end='')
	print(f'{layout.score.rollin:,}\t', end='')
	print(f'{layout.score.scissors:,}')
	if layout.left_usage > 0:
		total = layout.left_usage + layout.right_usage
		left_percent = (layout.left_usage / total) * 100
		right_percent = (layout.right_usage / total) * 100
		print(f'{left_percent:.2f} : {right_percent:.2f} \t {layout.total:,}')
	for row in layout.letters:
		print(row)

def save_best_result(best, result_path):
	file_path = os.path.join(result_path, BEST_RESULT_FILENAME)
	with open(file_path, 'w', encoding='utf-8') as f:
		for row in best.letters:
			print(row, file=f)
	print('...Saved')

def load_best_result(result_path):
	file_path = os.path.join(result_path, BEST_RESULT_FILENAME)
	with open(file_path, 'r', encoding='utf-8') as f:
		lines = [line.strip() for line in f if line.strip()]
	letters = [literal_eval(line) for line in lines[:3]]
	return Layout(letters)

if __name__ == '__main__':
	signal.signal(signal.SIGINT, cleanup)
	try:
		if len(sys.argv) != 2:
			print(f"Usage: {sys.argv[0]} <result_path>")
			sys.exit(1)

		result_path = sys.argv[1]
		result_path = os.path.expanduser(result_path)
		result_path = os.path.abspath(result_path)
		os.makedirs(result_path, exist_ok=True)

		# Analyze
		file_path = os.path.join(result_path, ANALYZE_RESULT_FILENAME)
		if os.path.exists(file_path):
			load_analysis_result(result_path)
		else:
			analyze_target(result_path)

		# Optimize
		init_score_state()
		file_path = os.path.join(result_path, BEST_RESULT_FILENAME)
		if os.path.exists(file_path):
			best = load_best_result(result_path)
		else:
			best = make_initial_layout()

		print(f'[Optimize]')
		res = optimize(best)
		print(f'\r\033[K...Done')

		if res.total > best.total:
			best = cur
			save_best_result(best, result_path)

		print_layout(best)

	except KeyboardInterrupt:
		cleanup(None, None)

	cleanup(None,None)
