def getMapHtml(updates, update, apiKey):
	""" Generates an HTML and JavaScript code segment using Google Maps API to plot the lat and lon on a map """
	
	locs = []
	for each in updates[1:]:
		locs.append((each.getLat(),each.getLon()))
	locs.append((update.getLat(),update.getLon()))
	
	### For every point in the list, format it into a string that can be inserted in to the JavaScript function
	allPoints = ''
	for each in locs:
		temp = '{lat: ' + str(each[0]) + ', lng: ' + str(each[1]) + '},'
		allPoints += temp
	allPoints = allPoints[:-1]
	
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