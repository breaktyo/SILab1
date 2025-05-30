import sys
import time
import math
import heapq
import csv
import bisect
import logging
import random
from collections import defaultdict

USE_QUICK_ROUTE_FINDER = True


def calculate_distance(lat1, lon1, lat2, lon2):
    R = 6371
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dlambda / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))
    return R * c

def convert_time_to_seconds(time_str: str) -> int:
    parts = time_str.split(':')
    parts = [int(p) for p in parts]
    if len(parts) == 2:
        hours, minutes = parts
        seconds = 0
    else:
        hours, minutes, seconds = parts
    return (hours * 3600 + minutes * 60 + seconds) % 86400

def convert_seconds_to_time(seconds: int) -> str:
    seconds = seconds % 86400
    h = seconds // 3600
    m = (seconds % 3600) // 60
    s = seconds % 60
    return f"{h:02d}:{m:02d}:{s:02d}"

def response_format(route):
    
    if not route:
        return
    itinerary = []
    first_trip = route[0]
    current_route = first_trip.line
    first_station = first_trip.start_stop
    first_time = first_trip.departure_time
    last_station = first_trip.end_stop
    last_time = first_trip.arrival_time
    for trip in route:
        if trip.line != current_route:
            itinerary.append((current_route, first_station, first_time, last_station, last_time))
            first_station = trip.start_stop
            first_time = trip.departure_time
            current_route = trip.line
        last_station = trip.end_stop
        last_time = trip.arrival_time
    itinerary.append((current_route, first_station, first_time, last_station, last_time))
    for line, start, start_time, end, end_time in itinerary:
        print(f"Linia: [{line}] Przystanek poczatkowy: [{start}], czas: [{convert_seconds_to_time(start_time)}] "
              f"Przystanek koncowy: [{end}], czas: [{convert_seconds_to_time(end_time)}]")


class StatusTracker:
    def __init__(self):
        self.start_time = time.time()
        logging.basicConfig(level=logging.INFO, format="%(message)s")
        self.logger = logging.getLogger("JourneyPlanner")
        
    def log(self, message: str):
        elapsed = time.time() - self.start_time
        self.logger.info(f"{message}")


class Trip:
    def __init__(self, row):
        self.id = row['id']
        self.company = row['company']
        self.line = row['line']
        self.departure_time = convert_time_to_seconds(row['departure_time'])
        self.arrival_time = convert_time_to_seconds(row['arrival_time'])
        self.start_stop = row['start_stop'].lower()
        self.end_stop = row['end_stop'].lower()
        self.start_stop_lat = float(row['start_stop_lat'])
        self.start_stop_lon = float(row['start_stop_lon'])
        self.end_stop_lat = float(row['end_stop_lat'])
        self.end_stop_lon = float(row['end_stop_lon'])
        
    def __repr__(self):
        return (f"Trip({self.line}: {self.start_stop} ({convert_seconds_to_time(self.departure_time)}) -> "
                f"{self.end_stop} ({convert_seconds_to_time(self.arrival_time)}))")
    

class TransportNetwork:
    def __init__(self, csv_path: str, tracker: StatusTracker):
        self.tracker = tracker
        self.trips_by_stop = defaultdict(list)
        self.trips_by_pair = defaultdict(list) 
        self.adjacent_stops = defaultdict(set) 
        self.stops_locations = {}
        self._import_data(csv_path)
        
    def _import_data(self, csv_path: str):
        self.tracker.log("Pobieranie danych")
        with open(csv_path, newline='', encoding='utf-8') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                trip = Trip(row)
                self.trips_by_stop[trip.start_stop].append(trip)
                self.trips_by_pair[(trip.start_stop, trip.end_stop)].append(trip)
                self.adjacent_stops[trip.start_stop].add(trip.end_stop)
                self.stops_locations[trip.start_stop] = (trip.start_stop_lat, trip.start_stop_lon)
                self.stops_locations[trip.end_stop] = (trip.end_stop_lat, trip.end_stop_lon)
        
        for stop, trips in self.trips_by_stop.items():
            trips.sort(key=lambda t: t.departure_time)
            self.trips_by_stop[stop] = (trips, [t.departure_time for t in trips])
        for key, trips in self.trips_by_pair.items():
            trips.sort(key=lambda t: t.departure_time)
        self.tracker.log("Dane wczytane")
        
    def find_available_trips(self, stop: str, current_time: int):
        """wolna wersja - wyszukuje binarnie te połączenia, które są dostępne"""
        result = []
        if stop not in self.trips_by_stop:
            return result
        trips, dep_times = self.trips_by_stop[stop]
        current_day_time = current_time % 86400
        idx = bisect.bisect_left(dep_times, current_day_time)
        for t in trips[idx:]:
            eff_dep = t.departure_time if t.departure_time >= current_day_time else t.departure_time + 86400
            eff_arr = t.arrival_time if t.arrival_time >= current_day_time else t.arrival_time + 86400
            if eff_dep < current_time:
                eff_dep += 86400
                eff_arr += 86400
            if eff_dep >= current_time:
                result.append((t, eff_dep, eff_arr))
        for t in trips[:idx]:
            eff_dep = t.departure_time + 86400
            eff_arr = t.arrival_time + 86400
            if eff_dep >= current_time:
                result.append((t, eff_dep, eff_arr))
        return result
    
    def find_quickest_trip(self, start_stop: str, end_stop: str, current_time: int):
        """szybka wersja - zwraca najszybsze połączenie jedno"""
        if (start_stop, end_stop) not in self.trips_by_pair:
            return None
        trips = self.trips_by_pair[(start_stop, end_stop)]
        dep_times = [t.departure_time for t in trips]
        current_day_time = current_time % 86400
        idx = bisect.bisect_left(dep_times, current_day_time)
        if idx < len(trips):
            trip = trips[idx]
            eff_dep = trip.departure_time if trip.departure_time >= current_day_time else trip.departure_time + 86400
            eff_arr = trip.arrival_time if trip.arrival_time >= current_day_time else trip.arrival_time + 86400
            if eff_dep < current_time:
                eff_dep += 86400
                eff_arr += 86400
            if eff_dep >= current_time:
                return trip, eff_dep, eff_arr
        if trips:
            trip = trips[0]
            eff_dep = trip.departure_time + 86400
            eff_arr = trip.arrival_time + 86400
            if eff_dep >= current_time:
                return trip, eff_dep, eff_arr
        return None

class RouteFinder:
    def __init__(self, network: TransportNetwork, tracker: StatusTracker, avg_speed_kmh: float = 20.0, transfer_wait_time: int = 300):
        self.network = network
        self.tracker = tracker
        self.avg_speed = avg_speed_kmh / 3600.0
        self.transfer_wait_time = transfer_wait_time
        
    def estimate_travel_time(self, current_stop: str, target_stop: str) -> float:
        if current_stop not in self.network.stops_locations or target_stop not in self.network.stops_locations:
            return 0
        lat1, lon1 = self.network.stops_locations[current_stop]
        lat2, lon2 = self.network.stops_locations[target_stop]
        distance = calculate_distance(lat1, lon1, lat2, lon2)
        return distance / self.avg_speed

    def find_optimal_route(self, start_stop: str, target_stop: str, start_time: int, mode='time'):
        start = time.time()
        self.tracker.log("Rozpoczeto przeszukiwanie A*")
        counter = 0
        L = 1000000
        initial_h = self.estimate_travel_time(start_stop, target_stop) if mode in ('t', 'time') else 0
        heap = [(initial_h, counter, 0, start_time, start_stop, None, [])]
        visited = {}
    
        def _get_next_trips(stop, current_time):
            if USE_QUICK_ROUTE_FINDER:
                if stop not in self.network.adjacent_stops:
                    return
                for neighbor in self.network.adjacent_stops[stop]:
                    res = self.network.find_quickest_trip(stop, neighbor, current_time)
                    if res is None:
                        continue
                    _trip, _eff_dep, _eff_arr = res
                    yield neighbor, _trip.line, _eff_dep, _eff_arr, _trip
            else:
                for _trip, _eff_dep, _eff_arr in self.network.find_available_trips(stop, current_time):
                    yield _trip.end_stop, _trip.line, _eff_dep, _eff_arr, _trip
    
        while heap:
            f, _, g, current_time, stop, current_line, path = heapq.heappop(heap)
            key = (stop, current_line)
            if key in visited and visited[key] <= g:
                continue
            visited[key] = g
            if stop == target_stop:
                comp_time = time.time() - start
                self.tracker.log("Przeszukiwanie A* skonczone")
                return path, g, comp_time
    
            for next_stop, next_line, eff_dep, eff_arr, trip in _get_next_trips(stop, current_time):
                counter += 1
                if mode in ('t', 'time'):
                    wait = eff_dep - current_time
                    travel = eff_arr - eff_dep
                    new_g = g + wait + travel
                    new_h = self.estimate_travel_time(next_stop, target_stop)
                    new_f = new_g + new_h
                else:
                    wait = eff_dep - current_time
                    if current_line is None:
                        additional = 0
                    else:
                        additional = 1 if (next_line != current_line or wait > self.transfer_wait_time) else 0
                    new_g = g + additional
                    new_f = new_g * L + eff_arr
                heapq.heappush(heap, (new_f, counter, new_g, eff_arr, next_stop, next_line, path + [trip]))
    
        comp_time = time.time() - start
        self.tracker.log("A* search completed - no path found")
        return None, float('inf'), comp_time


class OptimalTourFinder:
    def __init__(self, network: TransportNetwork, tracker: StatusTracker, route_finder: RouteFinder, mode='t'):
        self.network = network
        self.tracker = tracker
        self.route_finder = route_finder
        self.mode = mode.lower()
        self.cost_cache = {}
        
    def get_route_cost(self, start, end, start_time):
        key = (start, end, self.mode, start_time)
        if key in self.cost_cache:
            return self.cost_cache[key]
        if self.mode in ('t', 'time'):
            _, cost, _ = self.route_finder.find_optimal_route(start, end, start_time, mode='time')
        elif self.mode in ('p', 'transfers'):
            _, cost, _ = self.route_finder.find_optimal_route(start, end, start_time, mode='transfers')
        else:
            raise ValueError("Nieznany tryb optymalizacji")
        self.cost_cache[key] = cost
        return cost
    
    def create_cost_matrix(self, stops: list, start_time: int):
        self.tracker.log("Budowanie macierzy kosztów")
        n = len(stops)
        cost_matrix = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i == j:
                    cost_matrix[i][j] = 0
                else:
                    cost_matrix[i][j] = self.get_route_cost(stops[i], stops[j], start_time)
        self.tracker.log("Macierz kosztów zbudowana")
        return cost_matrix
    
    def calculate_tour_cost(self, solution, cost_matrix):
        total = 0
        n = len(solution)
        for i in range(n - 1):
            total += cost_matrix[solution[i]][solution[i + 1]]
        total += cost_matrix[solution[-1]][solution[0]]
        return total
    
    def generate_neighbors(self, solution, sample_size=None):
        neighbors = []
        n = len(solution)
        for i in range(1, n):
            for j in range(i + 1, n):
                new_sol = solution[:]
                new_sol[i], new_sol[j] = new_sol[j], new_sol[i]
                neighbors.append(tuple(new_sol))
        if sample_size is not None and len(neighbors) > sample_size:
            neighbors = random.sample(neighbors, sample_size)
        return neighbors
    
    def find_optimal_tour(self, start_stop: str, stops_to_visit: list, start_time: int,
              max_iterations=100, local_search_steps=50, tabu_size=None, sample_size=100):
        self.tracker.log("Rozpoczęcie rozwiązania problemu TSP")
        nodes = [start_stop] + stops_to_visit
        n = len(nodes)
        cost_matrix = self.create_cost_matrix(nodes, start_time)
        current_solution = tuple(range(n))
        best_solution = current_solution
        best_cost = self.calculate_tour_cost(current_solution, cost_matrix)
        tabu_list = []
        if tabu_size is None:
            tabu_size = len(stops_to_visit)
        total_iter = 0
        start_iter = time.time()
        for step in range(max_iterations):
            improved_local = False
            for op in range(local_search_steps):
                neighbors = self.generate_neighbors(list(current_solution), sample_size=sample_size)
                best_candidate = None
                best_candidate_cost = float('inf')
                for candidate in neighbors:
                    candidate_cost = self.calculate_tour_cost(candidate, cost_matrix)
                    if candidate in tabu_list and candidate_cost >= best_cost:
                        continue
                    if candidate_cost < best_candidate_cost:
                        best_candidate = candidate
                        best_candidate_cost = candidate_cost
                if best_candidate is None:
                    break
                current_solution = best_candidate
                tabu_list.append(best_candidate)
                if len(tabu_list) > tabu_size:
                    tabu_list.pop(0)
                if best_candidate_cost < best_cost:
                    best_solution = best_candidate
                    best_cost = best_candidate_cost
                    improved_local = True
                total_iter += 1
            if not improved_local:
                break
        comp_time = time.time() - start_iter
        self.tracker.log("Problem TSP rozwiązany")
        return best_solution, best_cost, comp_time, nodes, cost_matrix

def main():
    csv_path = "connection_graph.csv"
    tracker = StatusTracker()
    network = TransportNetwork(csv_path, tracker)
    route_finder = RouteFinder(network, tracker, transfer_wait_time=300)
    
    tracker.log("Wpisz dane wejściowe: przystabek startowy, przystanek/przystanki końcowe, tryb, czas startu")
    input_lines = [input().strip() for _ in range(4)]
    start_total = time.time()
    
    if ";" in input_lines[1]:
        start_stop = input_lines[0].lower()
        stops_to_visit = [s.strip().lower() for s in input_lines[1].split(";") if s.strip()]
        criterion = input_lines[2].lower()
        start_time = convert_time_to_seconds(input_lines[3])
        
        tour_finder = OptimalTourFinder(network, tracker, route_finder, mode=criterion)
        best_solution, tsp_cost, tsp_comp_time, nodes, cost_matrix = tour_finder.find_optimal_tour(
            start_stop, stops_to_visit, start_time,
            max_iterations=100, local_search_steps=50, tabu_size=None, sample_size=100
        )
        full_path = []
        total_leg_cost = 0
        total_leg_comp_time = 0
        current_time = start_time
        num_legs = len(best_solution)
        for i in range(num_legs):
            from_index = best_solution[i]
            to_index = best_solution[(i + 1) % num_legs]
            frm = nodes[from_index]
            to = nodes[to_index]
            if criterion in ('t', 'time'):
                path, leg_cost, leg_comp_time = route_finder.find_optimal_route(frm, to, current_time, mode='time')
            else:
                path, leg_cost, leg_comp_time = route_finder.find_optimal_route(frm, to, current_time, mode='transfers')
            if path is None:
                sys.stdout.write(f"Nie znaleziono połączenia pomiędzy {frm} a {to}\n")
                return
            full_path.extend(path)
            total_leg_cost += leg_cost
            total_leg_comp_time += leg_comp_time
            current_time = path[-1].arrival_time
            
        response_format(full_path)
        tracker.log(f"Łączny koszt trasy: {total_leg_cost}")
        
    else:
        start_stop = input_lines[0].lower()
        target_stop = input_lines[1].lower()
        criterion = input_lines[2].lower()
        start_time = convert_time_to_seconds(input_lines[3])
        if criterion in ('t', 'time'):
            path, cost, comp_time = route_finder.find_optimal_route(start_stop, target_stop, start_time, mode='time')
        else:
            path, cost, comp_time = route_finder.find_optimal_route(start_stop, target_stop, start_time, mode='transfers')
        if path is None:
            sys.stdout.write("Nie znaleziono trasy.\n")
            return
        
        response_format(path)
        tracker.log(f"Koszt trasy: {cost}")

    end_total = time.time()
    total_elapsed = end_total - start_total
    tracker.log(f"Łączny czas obliczeń: {total_elapsed:.4f} s")
        
if __name__ == "__main__":
    main()