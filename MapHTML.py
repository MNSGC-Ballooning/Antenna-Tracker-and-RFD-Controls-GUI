from PyQt4.QtWebKit import *
import sqlite3
from PyQt4.QtSql import *

def getMapHtml(updates, update, apiKey):
	""" Generates an HTML and JavaScript code segment using Google Maps API to plot the lat and lon on a map """
	
	locs = []
	for each in updates:
	# for each in updates[1:]:
		locs.append((each.getLat(),each.getLon()))
	locs.append((update.getLat(),update.getLon()))
	
	### For every point in the list, format it into a string that can be inserted in to the JavaScript function
	allPoints = ''
	for each in locs:
		temp = '{lat: ' + str(each[0]) + ', lng: ' + str(each[1]) + '},'
		allPoints += temp
	# allPoints = allPoints[:-1]
	print(allPoints)
	
	### The HTML and JavaScript is a formatted string, this allows for a Google Maps widget ###
	maphtml = '''
	<html><head>
	<meta name="viewport" content="initial-scale=1.0, user-scalable=no" />
	<style type="text/css">
		html { height: 100% }
		body { height: 100%; margin: 0; padding: 0 }
		#map { width: 100%; height: 100% }
	</style>
			<script async defer
			src="https://maps.googleapis.com/maps/api/js?key=''' + str(apiKey) + '''&callback=initialize">
			google.maps.event.addDomListener(window, "load", initialize)
	</script>
	<script type="text/javascript">
		var map, marker
		function initialize() {
			map = new google.maps.Map(document.getElementById("map"), {
				center: {lat: ''' + str(update.getLat()) + ''', lng: ''' + str(update.getLon()) + '''},
				zoom: 10,
				mapTypeId: 'terrain'
			})
			marker = new google.maps.Marker({
				map: map,
				position: map.getCenter(),
				draggable: false
			})
			pathCoordinates = [''' + str(allPoints) + '''];
			path = new google.maps.Polyline({
				map: map,
				path: pathCoordinates,
				geodesic: true,
				strokeColor: '#FF0000',
				strokeOpacity: 1.0,
				strokeWeight: 2
			});
		} 

	</script>
	</head>
	<body><div id="map"/></body>
	</html>
	'''
	
	# maphtml = """
	# <!DOCTYPE html>
	# <html>
	  # <head>
		# <meta name="viewport" content="initial-scale=1.0, user-scalable=no">
		# <meta charset="utf-8">
		# <title>Circles</title>
		# <style>
		  # html, body {
			# height: 100%;
			# margin: 0;
			# padding: 0;
		  # }
		  # map {
			# height: 100%;
		  # }
		# </style>
	  # </head>
	  # <body>
		# <div id="map"></div>
		# <script>
		  # // This example creates circles on the map

		  # // First, create an object containing LatLng and radius for each item.
		  # var balloon = {
			# payload: {
			  # center: {lat: """ + str(update.getLat()) + """, lng: """ + str(update.getLon())+"""},
			  # rad: 3000
			# }
		  # };

			# function initMap() {
			  # var myLatLng = {lat: """+str(update.getLat())+""", lng: """+str(update.getLon())+"""};

			  # var map = new google.maps.Map(document.getElementById('map'), {
				# zoom: 8,
				# center: myLatLng
			  # });

			  # var marker = new google.maps.Marker({
				# position: myLatLng,
				# map: map,
				# title: 'Current Position'
			  # });
			# }
		  
		# </script>
		# <script async defer
		# src="https://maps.googleapis.com/maps/api/js?key="""+str(apiKey)+"""&callback=initMap">
		# </script>
	  # </body>
	# </html>
	# """
	return maphtml

class CustomQWebPage(QWebPage):
	def __init__(self):
		super(CustomQWebPage, self).__init__()

	def javaScriptConsoleMessage(self,message,lineNumber,sourceID):
		print(message,lineNumber,sourceID)
		print("javascript console message^")

class ViewOnlyMap(QWebView):

	def __init__(self, apiKey, parent=None):
		super(ViewOnlyMap, self).__init__()
		self.apiKey = apiKey
		self.settings().setAttribute(QWebSettings.JavascriptEnabled, True)
		self.settings().setAttribute(QWebSettings.JavascriptCanOpenWindows, True)
		self.settings().setAttribute(QWebSettings.JavascriptCanAccessClipboard, True)
		self.settings().setAttribute(QWebSettings.DeveloperExtrasEnabled, True)
		self.CustomPage=CustomQWebPage()
		self.Coordinates=None
		self.finishedLoading = False

		self.setPage(self.CustomPage)
		self.loadFinished.connect(self.handleLoadFinished)
		self.set_code()
		
	def handleLoadFinished(self, ok):
		if ok:
			self.finishedLoading = True
			print("Page loaded successfully")
		else:
			print("Could not load page")
			
	def addPoint(self, lat, lon):
		self.CustomPage.mainFrame().evaluateJavaScript('NewLocationReceived({0},{1})'.format(lat, lon))

	def get_marker_coordinates(self):
		with sqlite3.connect("skateboard_progress_tracker.db") as db:
			cursor=db.cursor()
			sql="select SkateparkLongitude, SkateparkLatitude from Skatepark"
			cursor.execute(sql)
			self.Coordinates=cursor.fetchall()
		for coordinate in self.Coordinates:
			self.CustomPage.mainFrame().evaluateJavaScript('MarkersFromDatabase({0},{1})'.format(coordinate[0],coordinate[1]))

			print("Marker added")
			print(coordinate[0])
			print(coordinate[1])

	def set_code(self):
	
		self.html = '''
	<html><head>
	<meta name="viewport" content="initial-scale=1.0, user-scalable=no" />
	<style type="text/css">
		html { height: 100% }
		body { height: 100%; margin: 0; padding: 0 }
		#map { width: 100%; height: 100% }
	</style>
			<script async defer
			src="https://maps.googleapis.com/maps/api/js?key=''' + str(self.apiKey) + '''&callback=initialize">
			google.maps.event.addDomListener(window, "load", initialize)
	</script>
	<script type="text/javascript">
		var map;
		var poly;
		var pathCoordinates = [];
		var markers = [];
		function initialize() {
			map = new google.maps.Map(document.getElementById("map"), {
				center: {lat: ''' + str(45) + ''', lng: ''' + str(-93) + '''},
				zoom: 10,
				mapTypeId: 'terrain'
			});
			
			marker = new google.maps.Marker({
				title: 'New',
				position: {lat: ''' + str(45) + ''', lng: ''' + str(-93) + '''},
				map: map
			});
			markers.push(marker);
			pathCoordinates.push(marker.getPosition())
	
			poly = new google.maps.Polyline({
				map: map,
				path: [
					new google.maps.LatLng(37.4419, -122.1419), 
					new google.maps.LatLng(37.4519, -122.1519)
					],
				strokeColor: '#FF0000',
				strokeOpacity: 1.0,
				strokeWeight: 2
			});
		}
		
		function NewLocationReceived(LocationLat,LocationLon) {
			var newLoc = new google.maps.LatLng(LocationLat,LocationLon);
			markers[markers.length-1].setMap(null);
			var newMarker = new google.maps.Marker({
				title: LocationLat.toString().concat(",").concat((LocationLon.toString())),
				position: newLoc,
				animation: google.maps.Animation.DROP,
				map: map
			});
			markers.push(newMarker);
			
			pathCoordinates.push(newLoc)
			poly = new google.maps.Polyline({
				map: map,
				path: pathCoordinates,
				geodesic: true,
				strokeColor: '#FF0000',
				strokeOpacity: 1.0,
				strokeWeight: 2
			});
		}

	</script>
	</head>
	<body><div id="map"/></body>
	</html>
	'''

		self.setHtml(self.html)   